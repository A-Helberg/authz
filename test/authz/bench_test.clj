(ns authz.bench-test
  "The benchmark harness is code too. Build a small world and execute every
  benchmark scenario exactly once, asserting its sanity check — so
  `mise run bench` cannot silently rot while nobody is looking at it.
  No criterium timing happens here."
  (:require [authz.bench :as bench]
            [clojure.test :refer [deftest is testing]]))

(def ^:private small-world
  {:seed 7 :users 40 :orgs 2 :sites 10 :managers 8
   :submissions 60 :assignments 12 :docs 12})

(deftest every-benchmark-scenario-runs-and-passes-its-check
  (let [ctx (bench/build-world small-world)
        scenarios (bench/scenarios ctx)]
    (is (= 11 (count scenarios)))
    (doseq [{:keys [label thunk check]} scenarios]
      (testing label
        (is (check (thunk)))))))

(deftest scenarios-are-rebuildable-and-independent
  ;; two independent builds of the same seed agree on every scenario outcome
  (let [run-all (fn [] (mapv (fn [{:keys [thunk check]}] (boolean (check (thunk))))
                             (bench/scenarios (bench/build-world small-world))))]
    (is (= (run-all) (run-all)))
    (is (every? true? (run-all)))))
