(ns types
  (:require [clojure.core.logic :as l :refer [defne]]))

(def ^:dynamic psub) ; proper (!) subset

(def psub-rules (atom [])) ; rules defining psub relation
(defn reg-psub [r] (swap! psub-rules conj r))

(defn with-rules* [psub-rules f]
  (binding [psub (l/fne [a b] :tabled ([a b] (l/or* (map #(% a b) psub-rules))))]
    (doall (distinct (f)))))

(defmacro with-regs [& body]
 `(with-rules* @psub-rules #(do ~@body)))

; Considerations for registering rules
; psub expresses proper subset - it's important to guarantee
; transitive relation is bounded. (I think)

; Subset relationship between types a and b, defined as either
; 'a == 'b, 'a is a known proper subset of 'b, or transitive proper subset of 'b.
; TODO: decide between soft cut and not.
; Soft cut has a clear cut stop condition but is it guaranteed to find matches?
; This seems to fail when defne but should evaluate to :nothing
; I seem to be able to get good results with a limited number of matches,
; assuming I can the ordering right. But ordering seems to only work in case
; of defna that doesn't work in all cases..
(comment
 ; this fails to get any matches when sub is defined with defna
 (types/with-regs (l/run 1 [q] (types/sub q :num) (types/sub :nothing q) (types/sub q :int))))

(l/defne ^:tabled transitive [a b]
 ([x y]
  (l/!= x y)
  (psub x y))
 ([x z]
  ;(l/trace-lvars "before" x z)
  (l/fresh [y]
    (l/distincto [x y z])
    ;(l/trace-lvars "after" x z)
    (psub x y)
    (transitive y z))))

(l/defne sub [a b]
 ([x x])
 ([x y] (transitive x y)))

(defne app [f args e]
  ([[:fn [a] r] [p] r] (sub p a))
  ([[:fn [a1 a2] r] [p1 p2] r] (sub p1 a1) (sub p2 a2)))

(defn teval [env x e]
  (let [call (when (seq? x) (first x))]
    (cond
      (int? x) `(l/== ~x ~e)

      (= 'fn call)
      (let [[_ args & body] x
            r (gensym "r")]
       `(l/fresh [~@args ~r]
          (l/== ~e [:fn [~@args] ~r])
         ~(let [nenv (zipmap args (map (fn [a] `(l/fne [_#] ([x#] (l/== x# ~a)))) args))]
            (teval (merge env nenv) `(do ~@body) r))))
      
      (= 'do call)
      (let [xs (rest x)]
        (cond
          (empty? xs) `(l/== nil ~e)
          (empty? (rest xs)) (teval env (first xs) e)
          :else
          (let [syms (mapv (fn [_] (gensym "_")) (butlast xs))]
           `(l/fresh ~syms
             ~@(map #(teval env %1 %2) (butlast xs) syms)
             ~(teval env (last xs) e)))))

      (seq? x)
      (let [f (gensym "f") syms (mapv (fn [_] (gensym "e")) (rest x))]
       `(l/fresh [~f ~@syms]
         ~(teval env (first x) f)
         ~@(map #(teval env %1 %2) (rest x) syms)
          (app ~f ~syms ~e)))

      (and (symbol? x) (contains? env x)) `(~(env x) ~e)

      :else (throw (new IllegalArgumentException (str "wtf is " x))))))

(def global-env
 {'+ `(l/fne [_#] ([[:fn [:int :int] :int]]) ([[:fn [:num :num] :num]]))
  'inc `(l/fne [_#] ([[:fn [:int] :int]]))
  'identity `(l/fne [_#] ([[:fn [a#] a#]]))
  'map `(l/fne [_#] ([[:fn [[:fn [a#] b#] [:list a#]] [:list b#]]]))
})

(defmacro type [n exp]
  (let [e (gensym "e")]
   `(with-regs
      (l/run ~n [~e]
       ~(teval global-env exp e)))))

; Rules: core

(defne top-type [a b] ([a :any] (l/!= a :any)))
(reg-psub top-type)

(defne bottom-type [a b] ([:nothing b] (l/!= :nothing b)))
(reg-psub bottom-type)

; Rules: numbers

(defne int-literal [a b] ([x :int] (l/pred x int?)))
(reg-psub int-literal)

(defne int-is-num [a b] ([:int :num]))
(reg-psub int-is-num)

(defne float-literal [a b] ([x :float] (l/pred x float?)))
(reg-psub float-literal)

(defne float-is-num [a b] ([:float :num]))
(reg-psub float-is-num)

(defne ratio-literal [a b] ([x :ratio] (l/pred x ratio?)))
(reg-psub ratio-literal)

(defne ratio-is-num [a b] ([:ratio :num]))
(reg-psub ratio-is-num)

; Rules: functions

(l/defne sub-args [a b]
 ([[] []])
 ([['& xs] ['& ys]] (sub-args xs ys))
 ([[x . xs] [x . ys]] (sub-args xs ys))
 ([[x . xs] [y . ys]]
  (psub y x)
  (sub-args xs ys)))
; not registered, used in function-n-arity
; TODO: (= [:fn [:int & :int] :int]  [:fn [& :int] :int])
; TOOD: pattern matching turns vectors into lists breaking the convention

(l/defne function-n-arity [a b]
 ([[:fn largs lr] [:fn rargs rr]]
  (l/!= a b)
  (sub-args largs rargs)
  (l/conde [(l/== lr rr)] [(psub lr rr)])))
;(reg-psub function-n-arity)

; Rules: lists

(l/defne homogeneus-list [a b]
 ([[:list x] [:list y]] (l/!= x y) (psub x y)))
(reg-psub homogeneus-list) ; loops forever with current transitive impl

; Rules: vectors & tuples

; Rules: maps & structural