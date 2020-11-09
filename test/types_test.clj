(ns types-test
  (:require [clojure.test :refer [deftest is are]]
            [types :as target]))

(defn with-timeout* [t f]
  (let [fut (future (f))
        v (deref fut t ::timeout)]
    (future-cancel fut)
    v))

(defmacro with-timeout [& body]
 `(with-timeout* 400 (fn [] ~@body)))

(deftest test-type
  (are [x y] (= x (with-timeout (first (target/type y))))
   `int?
    (inc 1)

   '(:fn [_0] _0)
    (fn [x] x)

   `(:fn [int?] int?)
    (fn [x] (/ x) (inc x))

   `(:fn [int?] number?)
    (fn [x] (inc x) (/ x))

   `(:fn [(every? int? ~'%)] (every? int? ~'%))
    (fn [a] (map inc a))

   `(:fn [(:fn [~'_0] ~'_1) (every? ~'_0 ~'%)] ~'_1)
    (fn [a b] (map a b) (a (first b)))

   '(:fn [(:map :x _0 . _1)] _0)
    (fn [a] (get a :x))

  ;  '(:fn [(:map :x _0 . _1)] [:lit 1])
  ;   (fn [a] (assoc a :x 1) 1)

  ))