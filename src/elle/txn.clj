(ns elle.txn
  "Functions for cycle analysis over transactional workloads."
  (:require [clojure [pprint :refer [pprint]]
                      [set :as set]]
            [clojure.tools.logging :refer [info warn]]
            [clojure.java.io :as io]
            [dom-top.core :refer [loopr]]
            [elle [core :as elle]
                  [consistency-model :as cm]
                  [graph :as g]
                  [util :as util]
                  [viz :as viz]]
            [jepsen [history :as h]
                    [txn :as txn :refer [reduce-mops]]]
            [jepsen.history.fold :refer [loopf]]
            [tesser.core :as t]
            [unilog.config :refer [start-logging!]])
  (:import (io.lacuna.bifurcan IGraph
                               LinearMap
                               Map)
           (jepsen.history Op)))


(start-logging! {:console "%p [%d] %t - %c %m%n"})

(defn op-mops
  "A lazy sequence of all [op mop] pairs from a history."
  [history]
  (mapcat (fn [op] (map (fn [mop] [op mop]) (:value op))) history))

(t/deftransform keep-op-mops
  "A tesser fold over a history. For every op, and every mop in that op, calls
  `(f op mop])`. Passes non-nil results to downstream transforms."
  [f]
  (assoc downstream :reducer
         (fn reducer [acc ^Op op]
           (reduce (fn mop [acc mop]
                     (let [res (f op mop)]
                       (if (nil? res)
                         acc
                         (reducer- acc res))))
                   acc
                   (.value op)))))

(defn ok-keep
	"Given a function of operations, returns a sequence of that function applied
  to all ok operations. Returns nil iff every invocation of f is nil."
  [f history]
  (->> history
       h/oks
       (keep f)
       seq))

(defn all-keys
  "A sequence of all unique keys in the given history."
  [history]
  (->> history op-mops (map (comp second second)) distinct))

(def integer-types
  #{Byte Short Integer Long})

(defn assert-type-sanity
  "I cannot begin to convey the confluence of despair and laughter which I
  encountered over the course of three hours attempting to debug this issue.

  We assert that all keys have the same type, and that at most one integer type
  exists. If you put a mix of, say, Ints and Longs into this checker, you WILL
  question your fundamental beliefs about computers"
  [history]
  (let [int-val-types (->> (op-mops history)
                           (map (comp class last second))
                           (filter integer-types)
                           distinct)]
    (assert (<= (count int-val-types) 1)
            (str "History includes a mix of integer types for transaction values: " (pr-str int-val-types) ". You almost certainly don't want to do this.")))
  (let [key-types (->> (op-mops history)
                       (map (comp class second second))
                       distinct)]
    (assert (<= (count key-types) 1)
            (str "History includes a mix of different types for transaction keys: " (pr-str key-types) ". You almost certainly don't want to do this."))))

(defn failed-writes
  "Returns a map of keys to maps of failed write values to the operations which
  wrote them. Used for detecting aborted reads."
  [write? history]
  (h/fold history
          (loopf {:name :failed-writes}
                 ([failed {}]
                  [^Op op]
                  (recur
                    (if (h/fail? op)
                      (loopr [failed' failed]
                             [[f k v :as mop] (.value op)]
                             (if (write? f)
                               (recur (update failed' k assoc v op))
                               (recur failed')))
                      failed)))
                 ([failed {}]
                  [failed']
                  (recur (merge-with merge failed failed'))))))

(defn intermediate-writes
  "Returns a map of keys to maps of intermediate write values to the operations
  which wrote them. Used for detecting intermediate reads."
  [write? history]
  (h/fold history
          (loopf {:name :intermediate-writes}
                 ([im {}]
                  [^Op op]
                  ; Find intermediate writes for this particular txn by
                  ; producing two maps: intermediate keys to values, and
                  ; final keys to values in this txn. We shift elements
                  ; from final to intermediate when they're overwritten.
                  (recur (loopr [im'   im
                                 final {}]
                                [[f k v] (.value op)]
                                (if (write? f)
                                  (if-let [e (final k)]
                                    ; We have a previous write of k
                                    (recur (assoc-in im' [k e] op)
                                           (assoc final k v))
                                    ; No previous write
                                    (recur im' (assoc final k v)))
                                  ; Something other than an append
                                  (recur im' final))
                                im')))
                 ([im {}]
                  [im']
                  (recur (merge-with merge im im'))))))

(defn lost-update-cases
  "Takes a function write? which returns true iff an operation is a write, and
  a history. Returns a seq of error maps describing any lost updates found.
  Assumes writes are unique. Each map is of the form:

    {:key   The key in common
     :value The value read by all transactions
     :txns  A collection of completion ops for transactions which collided on
            this key and value.}

  Lost Update is a bit of a weird beast. I don't actually *have* a general
  definition of it: even in Adya, it's defined as 'Histories which look like
  H_lu', where H_lu is:

    w0(x0)
           r1(x0, 10)                          w1(x1, 14) c1
                      r2(x0, 10) w2(x2, 15) c2

    [x0 << x2 << x1]

  It stands to reason that the version order x2 << x1 and the precise order of
  T1 and T2 isn't necessary here: the essential problem is that T1 and T2 both
  read x0 and wrote different values of x, presumably based on x0. If this ever
  happens it could lead to the loss of the logical update T1 or T2 is
  performing.

  In cyclic terms, this must manifest as write-read edges from some transaction
  T0 to both T1 and T2 on the same key, (since both must read T0's write of x).

    +--wr--> T1
    |
    T0
    |
    +--wr--> T2

  WLOG, let x1 << x2. If we have the complete version order for x, we must also
  have a write-write edge from T1 -> T2 since both wrote x. However, since T2
  observed the state x0 which was overwritten by T1, we also have an rw edge
  from T2->T1. This forms a G2-item cycle:

    +--wr--> T1 <-+
    |        |    |
    T0       ww   rw
    |        V    |
    +--wr--> T2 --+

  We can already detect G2-item. However, we may not detect some instances of
  lost update because we may be missing some of these edges. Our version order
  inference is conservative, and especially for rw-registers may fail to
  capture many edges between versions. Even for list-append, if one of the
  writes is never read that version won't show up in the version order at all.

  What actually *matters* here is that two transactions read the same x0 and
  both wrote x, and committed. The precise order of writes to x doesn't matter.
  We can detect this directly, in linear time and space, by scanning the set of
  committed transactions and looking for any pair which both read some x=x0 and
  write x."
  [write? history]
  (loopr [; A map of keys to values to txns which read that key and value and
          ; wrote that key.
          txns (transient {})]
         [op history]
         (recur
           (if (not= :ok (:type op))
             txns
             (loopr [; A map of keys to the first value read
                     reads  (transient {})
                     ; And a set of keys we've written, so we don't
                     ; double-count
                     writes (transient #{})
                     txns   txns]
                    [[f k v] (:value op)]
                    (let [read-value (get reads k ::not-found)]
                      (if (and (write? f) (not (contains? writes k)))
                        ; We wrote k for the first time
                        (if (= read-value ::not-found)
                          ; Didn't read k; don't care
                          (recur reads writes txns)
                          ; We read and wrote k; this is relevant to our search
                          (let [txns-k    (get txns k (transient {}))
                                txns-k-v  (get txns-k read-value (transient []))
                                txns-k-v' (conj! txns-k-v op)
                                txns-k'   (assoc! txns-k read-value txns-k-v')]
                            (recur reads
                                   (conj! writes k)
                                   (assoc! txns k txns-k'))))
                        ; We read k
                        (if (= read-value ::not-found)
                          ; And this is our first (i.e. external) read of k
                          (recur (assoc! reads k v) writes txns)
                          ; We already read k
                          (recur reads writes txns))))
                    ; Return txns and move to next op
                    txns)))
         ; Now search for collisions
         (loopr [cases (transient [])]
                [[k v->txns]  (persistent! txns)
                 [v txns]     (persistent! v->txns)]
                (let [txns (persistent! txns)]
                  (recur
                    (if (<= 2 (count txns))
                      (conj! cases {:key   k
                                    :value v
                                    :txns  txns})
                      cases)))
                (let [cases (persistent! cases)]
                  (when (seq cases) cases)))))

(def cycle-explainer
  "This cycle explainer wraps elle.core's cycle explainer, and categorizes
  cycles based on what kinds of edges they contain; e.g. an all-ww cycle is
  :G0, one with realtime, ww, and wr edges is :G1c-realtime, etc."
  (reify elle/CycleExplainer
    (explain-cycle [_ pair-explainer cycle]
      (let [ex (elle/explain-cycle elle/cycle-explainer pair-explainer cycle)
            ; What types of relationships are involved here?
            type-freqs (frequencies (map :type (:steps ex)))
            realtime  (:realtime  type-freqs 0)
            process   (:process   type-freqs 0)
            ww        (:ww        type-freqs 0)
            wr        (:wr        type-freqs 0)
            rw        (:rw        type-freqs 0)
            ; Are any pair of rw's together?
            rw-adj?   (->> (:steps ex)
                           (cons (last (:steps ex))) ; For last->first edge
                           (map :type)
                           (partition 2 1)        ; Take pairs
                           (filter #{[:rw :rw]})  ; Find an rw, rw pair
                           seq
                           boolean)
            ; We compute a type based on data dependencies alone
            data-dep-type (cond (= 1 rw) "G-single"
                                (< 1 rw) (if rw-adj?
                                           "G2-item"
                                           "G-nonadjacent")
                                (< 0 wr) "G1c"
                                (< 0 ww) "G0"
                                true (throw (IllegalStateException.
                                              (str "Don't know how to classify"
                                                   (pr-str ex)))))
            ; And tack on a -process or -realtime tag if there are those types
            ; of edges.
            subtype (cond (< 0 realtime) "-realtime"
                          (< 0 process)  "-process"
                          true           "")]
        ; (prn :type (keyword (str data-dep-type subtype)))
        (assoc ex :type (keyword (str data-dep-type subtype)))))

    (render-cycle-explanation [_ pair-explainer
                               {:keys [type cycle steps] :as ex}]
      (elle/render-cycle-explanation
        elle/cycle-explainer pair-explainer ex))))

(defn nonadjacent-rw
  "This fn ensures that no :rw is next to another by testing successive edge
  types. In addition, we ensure that the first edge in the cycle is not an rw.
  Cycles must have at least two edges, and in order for no two rw edges to be
  adjacent, there must be at least one non-rw edge among them. This constraint
  ensures a sort of boundary condition for the first and last nodes--even if
  the last edge is rw, we don't have to worry about violating the nonadjacency
  property when we jump to the first."
  ([v] [0 true]) ; Our accumulator here is a map of rw-count, last-was-rw.
  ([[n last-was-rw?] path rel v']
   ; It's fine to follow *non* rw links, but if you've only
   ; got rw, and we just did one, this path is invalid.
   (let [rw? (= (g/bset :rw) rel)]
     (if (and last-was-rw? rw?)
       :elle.graph/invalid
       [(if rw? (inc n) n) rw?]))))

(def cycle-type-priorities
  "A map of cycle types to approximately how bad they are; low numbers are more
  interesting/severe anomalies"
  (->> [:G0
        :G1c
        :G-single
        :G-nonadjacent
        :G2-item
        :G0-process
        :G1c-process
        :G-single-process
        :G-nonadjacent-process
        :G2-item-process
        :G0-realtime
        :G1c-realtime
        :G-single-realtime
        :G-nonadjacent-realtime
        :G2-item-realtime]
       (map-indexed (fn [i t] [t i]))
       (into {})))

(def cycle-anomaly-specs
  "We define a specification language for different anomaly types, and a small
   interpreter to search for them. An anomaly is specified by a map including:

     :rels         A set of relationships which must intersect with every
                   edge in the cycle

     - or -

     :first-rels   A set of relationships which must intersect with the first
                   edge in the cycle.
     :rest-rels    A set of relationships which must intersect with remaining
                   edges.

     - and optionally -

     :filter-ex    A predicate over a cycle explanation. We use this
                   to restrict cycles to e.g. *just* G2 instead of G-single."
  (sorted-map-by
    (fn [a b] (compare (cycle-type-priorities a 100)
                       (cycle-type-priorities b 100)))
    :G0        {:rels #{:ww}}
    ; We want at least one wr edge, so we specify that as first-rels.
    :G1c       {:first-rels #{:wr}
                :rest-rels  #{:ww :wr}}
    ; Likewise, G-single starts with the anti-dependency edge. This anomaly is
    ; read skew, and is proscribed by SI.
    :G-single  {:first-rels  #{:rw}
                :rest-rels   #{:ww :wr}}

    ; Per Cerone & Gotsman
    ; (http://software.imdea.org/~gotsman/papers/si-podc16.pdf), strong session
    ; SI is equivalent to allowing only cycles with 2+ adjacent rw edges.
    ; G-single is a special case, where there is exactly one such edge. We
    ; define a more general form of G-single, which we call G-nonadjacent: a
    ; cycle which has rw edges, and no pair of rw edges are adjacent.
    :G-nonadjacent {:rels              #{:ww :wr :rw}
                    :with              nonadjacent-rw
                    ; We need more than one rw edge for this to count;
                    ; otherwise it's G-single.
                    :filter-path-state (fn [ps] (< 1 (first (:state ps))))}

    ; G2-item, likewise, starts with an anti-dep edge, but allows more, and
    ; insists on being G2, rather than G-single. Not bulletproof, but G-single
    ; is worse, so I'm OK with it.
    ;
    ; Note that right now we have no model for predicate dependencies, so
    ; *everything* we find is G2-item.
    :G2-item   {:first-rels  #{:rw}
                :rest-rels   #{:ww :wr :rw}
                :filter-ex   (comp #{:G2-item} :type)}

    ; A process G0 can use any number of process and ww edges--process is
    ; acyclic, so there's got to be at least one ww edge. We also demand the
    ; resulting cycle be G0-process, to filter out plain old G0s.
    :G0-process        {:rels        #{:ww :process}
                        :filter-ex   (comp #{:G0-process} :type)}
    ; G1c-process needs at least one wr-edge to distinguish itself from
    ; G0-process.
    :G1c-process       {:first-rels  #{:wr}
                        :rest-rels   #{:ww :wr :process}
                        :filter-ex   (comp #{:G1c-process} :type)}
    ; G-single-process starts with an anti-dep edge and can use processes from
    ; there.
    :G-single-process  {:first-rels  #{:rw}
                        :rest-rels   #{:ww :wr :process}
                        :filter-ex   (comp #{:G-single-process} :type)}
    ; G2-process starts with an anti-dep edge, and allows anything from there.
    ; Plus it's gotta be G2-process, so we don't report G2s or G-single-process
    ; etc.
    :G2-item-process   {:first-rels  #{:rw}
                        :rest-rels   #{:ww :wr :rw :process}
                        :filter-ex   (comp #{:G2-item-process} :type)}

    ; Ditto for realtime
    :G0-realtime        {:rels        #{:ww :realtime}
                         :filter-ex   (comp #{:G0-realtime} :type)}
    :G1c-realtime       {:first-rels  #{:wr}
                         :rest-rels   #{:ww :wr :realtime}
                         :filter-ex   (comp #{:G1c-realtime} :type)}
    :G-single-realtime  {:first-rels  #{:rw}
                         :rest-rels   #{:ww :wr :realtime}
                         :filter-ex   (comp #{:G-single-realtime} :type)}
    :G2-item-realtime   {:first-rels  #{:rw}
                         :rest-rels   #{:ww :wr :rw :realtime}
                         :filter-ex   (comp #{:G2-item-realtime} :type)}))

(def cycle-types
  "All types of cycles we can detect."
  (into (set (keys cycle-anomaly-specs))
        ; We don't explicitly specify these, but the explainer will spit them
        ; out. I don't know whether we should count them as REAL exactly, so...
        #{:G-nonadjacent-process
          :G-nonadjacent-realtime}))

(def process-anomaly-types
  "Anomaly types involving process edges."
  (set (filter (comp (partial re-find #"-process") name) cycle-types)))

(def realtime-anomaly-types
  "Anomaly types involving realtime edges."
  (set (filter (comp (partial re-find #"-realtime") name) cycle-types)))

(def unknown-anomaly-types
  "Anomalies which cause the analysis to yield :valid? :unknown, rather than
  false."
  #{:empty-transaction-graph
    :cycle-search-timeout})

(defn prohibited-anomaly-types
  "Takes an options map with

      :consistency-models   A collection of consistency models we expect hold
      :anomalies            A set of additional, specific anomalies we don't
                            want to see

  and returns a set of anomalies which would constitute a test failure.
  Defaults to {:consistency-models [:strict-serializable]}"
  [opts]
  (set/union (cm/all-anomalies-implying (:anomalies opts))
             (cm/anomalies-prohibited-by
               (:consistency-models opts [:strict-serializable]))))

(defn reportable-anomaly-types
  "Anomalies worth reporting on, even if they don't cause the test to fail."
  [opts]
  (set/union (prohibited-anomaly-types opts)
             unknown-anomaly-types))

(defn additional-graphs
  "Given options, determines what additional graphs we'll need to consider for
  this analysis. Options:

      :consistency-models   A collection of consistency models we expect hold
      :anomalies            A set of additional, specific anomalies we don't
                            want to see
      :additional-graphs    If you'd like even more dependencies"
  [opts]
  (let [ats (reportable-anomaly-types opts)]
    (-> ; If we need realtime, use realtime-graph. No need to bother
        ; with process, cuz we'll find those too.
        (cond (seq (set/intersection realtime-anomaly-types ats))
              #{elle/realtime-graph}

              ; If we're looking for any process anomalies...
              (seq (set/intersection process-anomaly-types ats))
              #{elle/process-graph}

              ; Otherwise, the usual graph is fine.
              true nil)
        ; Tack on any other requested graphs.
        (into (:additional-graphs opts)))))

(defn filtered-graphs
  "Takes a graph g. Returns a function that takes a set of relationships, and
  yields g filtered to just those relationships. Memoized.

  This means keeping around a fair bit of redundant materialized
  information; I can forsee this causing memory pressure later. It might be
  worthwhile to materialize just one or two of these graphs, do a search for a
  particular kind of cycle across ALL SCCs, then move on to the next graph,
  etc, so we can keep only the graphs we need in memory. On the other hand,
  that might waste more time doing SCC-specific precomputation. Not sure."
  [graph]
  (memoize (fn [rels] (g/project-relationships rels graph))))

(defn warm-filtered-graphs!
  "I thought memoizing this and making it lazy was a good idea, and it might be
  later, but it also pushes a BIG chunk of work into initial cycle search---the
  timeout fires and kills a whole bunch of searches because the graph isn't
  computed yet, and that's silly. So instead, we explicitly precompute these.

  Returns fg, but as a side effect, with all the relevant filtered graphs for
  our search precomputed."
  [fg]
  (->> (vals cycle-anomaly-specs)
       (mapcat (juxt :rels :first-rels :rest-rels))
       (remove nil?)
       set
       (pmap fg)
       dorun)
  fg)

(def cycle-search-timeout
  "How long, in milliseconds, to look for a certain cycle in any given SCC."
  1000)

(defn cycle-cases-in-scc-fallback
  "This finds SOME cycle via DFS in an SCC as a fallback, in case our BFS gets
  stuck. We invoke this if our search times out."
  [g fg pair-explainer scc]
  (let [c (loop [rels [#{:ww}
                       #{:ww :realtime :process}
                       #{:ww :wr}
                       #{:ww :wr :realtime :process}
                       #{:ww :wr :rw}
                       #{:ww :wr :rw :realtime :process}]]
            (if-not (seq rels)
              ; Out of projections; fall back to the total scc, which
              ; MUST have a cycle.
              (g/fallback-cycle g scc)

              ; Try the graph which has just those relationships and
              ; that particular SCC
              (if-let [sub-scc (-> ^IGraph (fg (first rels))
                                   (.select (g/->bset scc))
                                   (g/strongly-connected-components)
                                   first)]
                ; Hey, we've got a smaller SCC to focus on!
                (g/fallback-cycle g sub-scc)
                ; No dice
                (recur (next rels)))))]
    (elle/explain-cycle cycle-explainer
                        pair-explainer
                        c)))

(defn cycle-cases-in-scc
  "Searches a single SCC for cycle anomalies. See cycle-cases."
  [opts g fg pair-explainer scc]
  (let [; We're going to do a partial search which can time out. If that
        ; happens, we want to preserve as many of the cycles that we found as
        ; possible, and offer an informative error message. These two variables
        ; help us do that.
        types  (atom []) ; What kind of anomalies have we searched for?
        cycles (atom [])] ; What anomalies did we find?
    (util/timeout
      (:cycle-search-timeout opts cycle-search-timeout)
      ; If we time out...
      (let [types  @types
            cycles @cycles]
        (info "Timing out search for" (peek types) "in SCC of" (count scc)
              "transactions (checked" types ")")
        ;(info :scc
        ;      (with-out-str (pprint scc)))
        ; We generate two types of anomalies no matter what. First, an anomaly
        ; that lets us know we failed to complete the search. Second, a
        ; fallback cycle so there's SOMETHING from this SCC.
        (concat [{:type               :cycle-search-timeout
                  :anomaly-spec-type  (peek types)
                  :does-not-contain   (drop-last types)
                  :scc-size           (count scc)}
                 (cycle-cases-in-scc-fallback g fg pair-explainer scc)]
                ; Then any cycles we already found.
                cycles))
      ; Now, try each type of cycle we can search for
      ;
      ; This is basically a miniature interpreter for the anomaly specification
      ; language we defined above. It's... clean, but it also duplicates a lot
      ; of work--for instance, a G1c cycle will be detected three times, by
      ; G1c, G1c-process, and G1c-realtime; we then have to ignore 2 of those
      ; in the filter step. I don't think this is super expensive, but future
      ; self, if you're looking at a profiler and trying to find constant
      ; factors to optimize, this might be a good spot to start.
      ;
      ; TODO: many anomalies imply others. We should use the dependency graph to
      ; check for special-case anomalies before general ones, and only check for
      ; the general ones if we can't find special-case ones. e.g. if we find a
      ; g-single, there's no need to look for g-nonadjacent.
      ;(info "Checking scc of size" (count scc))
      (doseq [[type spec] cycle-anomaly-specs]
        ; (info "Checking for" type)
        ; For timeout reporting, we keep track of what type of anomaly
        ; we're looking for.
        (swap! types conj type)

        ; First, find a cycle using the spec.
        (let [;_      (prn)
              ; _      (prn :spec type spec)
              ; Restrict the graph to certain relationships, if necessary.
              g     (if-let [rels (:rels spec)]
                      (do ;(info "getting restricted graph")
                          (fg rels))
                      g)
              ; Now, we have three cycle-finding strategies...
              ;_     (info "Finding cycle")
              cycle (cond (:with spec)
                          (g/find-cycle-with (:with spec)
                                             (:filter-path-state spec)
                                             g scc)

                          (:rels spec)
                          (g/find-cycle g scc)

                          true
                          (g/find-cycle-starting-with
                            (fg (:first-rels spec))
                            (fg (:rest-rels spec))
                            scc))]
          ;_ (info "Done with cycle search")
          (when cycle
            ; (info "Explaining cycle")
            ; Explain the cycle
            (let [ex (elle/explain-cycle cycle-explainer pair-explainer
                                         cycle)
                  ; _ (info "Filtering explanation")
                  ; _ (prn :explanation ex)
                  ; Make sure it passes the filter, if we have one.
                  ex (if-let [p (:filter-ex spec)]
                       (when (p ex) ex)
                       ex)]
              ; And record that we found it
              (swap! cycles conj ex)))))
      @cycles)))

(defn cycle-cases
  "We take the unified graph, a pair explainer that can justify relationships
  between pairs of transactions, and a collection of strongly connected
  components in the unified graph. We proceed to find allllll kinds of cycles,
  returning a map of anomaly names to sequences of cycle explanations for each.
  We find:

  :G0                 ww edges only
  :G1c                ww, at least one wr edge
  :G-single           ww, wr, exactly one rw
  :G2-item            ww, wr, 2+ rw

  :G0-process         G0, but with process edges
  ...

  :G0-realtime        G0, but with realtime edges
  ..."
  [opts graph pair-explainer sccs]
  (let [fg (-> (filtered-graphs graph) warm-filtered-graphs!)]
    (->> sccs
         (mapcat (partial cycle-cases-in-scc opts graph fg pair-explainer))
         ; And group them by type
         (group-by :type))))

(defn cycles
  "Takes an options map, including a collection of expected consistency models
  :consistency-models, a set of additional :anomalies, an analyzer function,
  and a history. Analyzes the history and yields the analysis, plus an anomaly
  map like {:G1c [...]}."
  [opts analyzer history]
  (let [; Analyze the history
        {:keys [graph explainer sccs] :as analysis}
        (elle/check- analyzer history)

        ; Find anomalies
        anomalies (cycle-cases opts graph explainer sccs)]
    ;(prn :cycles)
    ;(pprint anomalies)
    ; Merge our cases into the existing anomalies map.
    (update analysis :anomalies merge anomalies)))

(defn cycles!
  "Like cycles, but writes out files as a side effect. Only writes files for
  relevant anomalies."
  [opts analyzer history]
  (let [analysis (cycles opts analyzer history)
        anomalies (select-keys (:anomalies analysis)
                               (reportable-anomaly-types opts))]
    ; First, text files.
    (doseq [[type cycles] anomalies]
      (when (cycle-types type)
        (elle/write-cycles! (assoc opts
                                   :pair-explainer  (:explainer analysis)
                                   :cycle-explainer cycle-explainer
                                   :filename        (str (name type) ".txt"))
                            cycles)))

    ; Then (in case they break), GraphViz plots.
    (when-let [d (:directory opts)]
      ; We do a directory for SCCs...
      (viz/plot-analysis! analysis (io/file d "sccs") opts)

      ; Then for each class of anomaly...
      (dorun
        (pmap (fn [[type cycles]]
                (when (cycle-types type)
                  ; plot-analysis! expects a list of sccs, which it's gonna go
                  ; through and plot. We're going to give it just the component
                  ; it needs to show each particular cycle explanation.
                  (let [sccs (map (comp set :cycle) cycles)]
                    (viz/plot-analysis! (assoc analysis :sccs sccs)
                                        (io/file d (name type))
                                        opts))))
        anomalies)))

    ; And return analysis
    analysis))

(defn result-map
  "Takes options, including :anomalies and :consistency-models, which define
  what specific anomalies and consistency models to look for, and a map of
  anomaly names to anomalies, and returns a map of the form...

  {:valid?        true | :unknown | false
   :anomaly-types [:g1c ...]
   :anomalies     {:g1c [...] ...}
   :impossible-models #{:snapshot-isolation ...}}"
  [opts anomalies]
  ;(info :anomalies anomalies)
  ;(info :reportable-anomaly-types (reportable-anomaly-types opts))
  (let [bad         (select-keys anomalies (prohibited-anomaly-types opts))
        reportable  (select-keys anomalies (reportable-anomaly-types opts))]
    (if (empty? reportable)
      ; TODO: Maybe return anomalies and/or a boundary here too, and just not
      ; flag them as invalid? Maybe? I dunno, might be noisy, especially if we
      ; expect to see them all the time.
      {:valid? true}
      (merge {:valid?            (cond (seq bad)          false
                                       (seq reportable)   :unknown
                                       true               true)
              :anomaly-types     (sort (keys reportable))
              :anomalies         reportable}
             (cm/friendly-boundary (keys anomalies))))))

(defn wr-txns
  "A lazy sequence of write and read transactions over a pool of n numeric
  keys; every write is unique per key. Options:

    :key-dist             Controls probability distribution for keys being
                          selected for a given operation. Choosing :uniform
                          means every key has an equal probability of appearing.
                          :exponential means that key i in the current key pool
                          is k^i times more likely than the first key to be
                          chosen. Defaults to :exponential.

    :key-dist-base        The base for an exponential distribution. Defaults
                          to 2, so the first key is twice as likely as the
                          second, which is twice as likely as the third, etc.

    :key-count            Number of distinct keys at any point. Defaults to
                          10 for exponential, 3 for uniform.

    :min-txn-length       Minimum number of operations per txn

    :max-txn-length       Maximum number of operations per txn

    :max-writes-per-key   Maximum number of operations per key"

  ([opts]
   (let [key-dist  (:key-dist  opts :exponential)
         key-count (:key-count opts (case key-dist
                                      :exponential 10
                                      :uniform     3))]
     (wr-txns (assoc opts
                     :key-dist  key-dist
                     :key-count key-count)
              {:active-keys (vec (range key-count))})))
  ([opts state]
   (lazy-seq
     (let [min-length           (:min-txn-length      opts 1)
           max-length           (:max-txn-length      opts 2)
           max-writes-per-key   (:max-writes-per-key  opts 32)
           key-dist             (:key-dist            opts :exponential)
           key-dist-base        (:key-dist-base       opts 2)
           key-count            (:key-count           opts (case key-dist
                                                             :exponential 3
                                                             :uniform     3))
           ; Choosing our random numbers from this range converts them to an
           ; index in the range [0, key-count).
           key-dist-scale       (-> (Math/pow key-dist-base key-count)
                                    (- 1)
                                    (* key-dist-base)
                                    (/ (- key-dist-base 1)))
           length               (+ min-length (rand-int (- (inc max-length)
                                                           min-length)))
           [txn state] (loop [length  length
                              txn     []
                              state   state]
                         (let [^java.util.List active-keys
                               (:active-keys state)]
                           (if (zero? length)
                             ; All done!
                             [txn state]
                             ; Add an op
                             (let [f (rand-nth [:r :w])
                                   ki (-> (rand key-dist-scale)
                                              (+ key-dist-base)
                                              Math/log
                                              (/ (Math/log key-dist-base))
                                              (- 1)
                                              Math/floor
                                              long)
                                   k (case key-dist
                                       :uniform     (rand-nth active-keys)
                                       :exponential (nth active-keys ki))
                                   v (when (= f :w) (get state k 1))]
                               (if (and (= :w f)
                                        (< max-writes-per-key v))
                                 ; We've updated this key too many times!
                                 (let [i  (.indexOf active-keys k)
                                       k' (inc (reduce max active-keys))
                                       state' (update state :active-keys
                                                      assoc i k')]
                                   (recur length txn state'))
                                 ; Key is valid, OK
                                 (let [state' (if (= f :w)
                                                (assoc state k (inc v))
                                                state)]
                                   (recur (dec length)
                                          (conj txn [f k v])
                                          state')))))))]
       (cons txn (wr-txns opts state))))))

(defn gen
  "Takes a sequence of transactions and returns a sequence of invocation
  operations."
  [txns]
  (map (fn [txn] {:type :invoke, :f :txn, :value txn}) txns))
