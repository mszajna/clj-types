(ns types
  (:require [clojure.core.logic :as l :refer [defne]]))

(def ^:dynamic psub) ; proper (!) subset

(def global-psub-rules (atom [])) ; rules defining psub relation
(defn reg-psub [r] (swap! global-psub-rules conj r))

(defn interruptible [a]
  (when (Thread/interrupted) (throw (new InterruptedException)))
  a)

(defn make-psub [psub-rules]
  (l/fne [a b depth] :tabled
    ([a b d]
      interruptible
      (l/trace-lvars "psub" a b)
      (l/or* (map #(% a b d) psub-rules)))))

(defn with-rules* [psub-rules f]
  (binding [psub (make-psub psub-rules)]
    (doall (distinct (f)))))

(defmacro with-regs [& body]
 `(with-rules* @global-psub-rules #(do ~@body)))

; Assigning types to vars

(defn set-type! [var type]
  (alter-meta! var assoc :type type))

(defn get-var-type [qsym]
  (-> qsym resolve meta :type))

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
 (types/with-regs (l/run 1 [q] (types/sub q `number?) (types/sub :nothing q) (types/sub q `int?))))
; Update: I got the conda business wrong!
; It goes through each alternative evaluating the first clause. First that succeeds locks
; conda in, but remaining clauses still have to succeed themselves.
; No further alternatives are considered.
; (conda [succeed fail] [succeed]) for instance, fails.
; And so does:
; (l/run 1 [q]
;   (l/conda [(l/== q 1)] [(l/== q 2)])
;   (l/== q 2))
; Which looks like a deal breaker

; Core relations

; (defn sub [a b depth]
;   (l/conde
;     [(l/== a b)]
;     [(l/!= a b) (psub a b)]
;     [(l/fresh [t] (l/distincto [a t b]) (psub a t) (sub t b))]))

(defne sub [a b depth]
  ([x x _])
  ([x y [_ . d]] (psub x y d))
  ([x z [_ . d]] (l/fresh [y] (psub x y d) (sub y z d))))

(def d (range 5))

(defne app [f args e]
  ([[:fn [a] r] [p] r] (sub p a d))
  ([[:fn [a1 a2] r] [p1 p2] r] (sub p1 a1 d) (sub p2 a2 d)))

; The 'type' macro

(defn var-name [env sym]
  (when-let [v (and (symbol? sym) (resolve env sym))]
    (let [nm (:name (meta v))
          nsp (.getName ^clojure.lang.Namespace (:ns (meta v)))]
      (symbol (name nsp) (name nm)))))

(defn teval [env x e]
  (let [call (when (seq? x) (first x))]
    (cond
      (or (number? x) (string? x))
     `(l/== ~x ~e)

      (= 'fn call)
      (let [[_ args & body] x
            nenv (gensym "nenv")
            r (gensym "r")]
       `(l/fresh [~@args ~r]
          (l/== ~e [:fn [~@args] ~r])
         ~(teval (merge env (zipmap args (repeat true))) `(do ~@body) r)))
      
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
      (let [f (gensym "f")
            syms (mapv (fn [_] (gensym "e")) (rest x))]
       `(l/fresh [~f ~@syms]
         ~(teval env (first x) f)
         ~@(map #(teval env %1 %2) (rest x) syms)
          (app ~f ~syms ~e)))

      (vector? x)
      (let [syms (mapv (fn [_] (gensym "e")) x)]
       `(l/fresh [~@syms]
         ~@(map #(teval env %1 %2) x syms)
          (l/== ~e [:vector ~@syms])))

      (symbol? x)
      (if-let [name (var-name env x)]
       `((get-var-type (quote ~name)) ~e)
       `(l/== ~x ~e))

      :else (throw (new IllegalArgumentException (str "wtf is " x))))))

(defmacro type [n exp]
  (let [e (gensym "e")]
   `(with-regs
      (l/run ~n [~e]
       ~(teval &env exp e)))))

; TODO: teval above tries to satisfy all expressions at once. While this
; is cool in principle, ideally I should be able to follow the execution order
; and pinpoint the exact place that causes trouble.

; ######## RULES ########################
; #######################################

; Rules: top and bottom
; TODO: top corresponds to unbound lvar
; TODO: bottom corresponds to logic failure
; Q: Do I even need these rules?

; (defne top-type [a b] ([a :any] (l/!= a :any)))
; (reg-psub top-type)

; (defne bottom-type [a b] ([:nothing b] (l/!= :nothing b)))
; (reg-psub bottom-type)

; Rules: numbers

(defne int-literal [a b _] ([x `int? _] (l/pred x int?)))
(reg-psub int-literal)

(defne int-is-num [a b d] ([`int? `number? d]))
(reg-psub int-is-num)
(comment (reg (int? %) => (number? %)))

(defne float-literal [a b _] ([x `float? _] (l/pred x float?)))
(reg-psub float-literal)

(defne float-is-num [a b _] ([`float? `number? _]))
(reg-psub float-is-num)

(defne ratio-literal [a b _] ([x `ratio? _] (l/pred x ratio?)))
(reg-psub ratio-literal)

(defne ratio-is-num [a b _] ([`ratio? `number? _]))
(reg-psub ratio-is-num)

; Rules: functions

(defne sub-args [a b depth max-args]
 ([[] [] _ _])
 ([['& xs] ['& ys] d _] (sub xs ys d)) 
 ([[x . xs] [x . ys] d [_ . a]] (sub-args xs ys d a))
 ([[x . xs] [y . ys] d [_ . a]]
  (sub y x d)
  (sub-args xs ys d a)))
; TODO: (= [:fn [`int? & `int?] `int?]  [:fn [& `int?] `int?])
; TOOD: pattern matching turns vectors into lists breaking the convention

(def max-args 20) ; maximum number of arguments supported by Clojure functions

(defne function-n-arity [a b depth]
 ([[:fn largs lr] [:fn rargs rr] d]
  (sub-args largs rargs d (range max-args))
  (sub lr rr d)))
(reg-psub function-n-arity)
(comment (reg (fn largs lret) (=> rargs largs) (=> lret rret) => (fn rargs rret)))

; Rules: lists

(defne homogeneous-collection [a b depth]
 ([[`every? x '%] [`every? y '%] d] (sub x y d)))
(reg-psub homogeneous-collection)
(comment (reg (every? a %) (=> a b) => (every? b %)))

; Considerations:
; Up to homogeneous-list rule above, the space of types was limited and it was
; possible to traverse it all. Therefore, it was possible to disprove an expression.
; The rule above introduces infinite number of new types with growing nested lists.
; When given two incompatible types (sub `int? [`every? a]), he logic engine tries to
; traverse it all and obviously gets caught in an infinite loop.

; It is becoming obvious that being able to disprove an expession is as important as to
; prove it. Java has a type hierarchy where `int? and `every? will never unify. I wanted
; to avoid it but can I?

; (psub b a) implies !(sub a b) but this is a limited solution. In many cases the two
; have no declared relationship.

; This loops forever:
; (types/with-regs (l/run 1 [a] (l/fresh [x] (types/psub a [`every? x]) (types/psub `number? a))))))
; The engine isn't able to figure out there is no such x, such that (psub `number? [`every? x])
; But then (l/run 1 [a] (types/psub `number? [`every? a]))
; completes with no problems?
; And so does (l/run 1 [a] (l/fresh [x] (types/psub `number? a) (types/psub a [`every? x])))

; Rules: vectors / tuples

(defne every-sub [coll p depth]
 ([[] _ d])
 ([[x . xs] p d]
  (sub x p d)
  (every-sub xs p d)))

(defne vector-as-every [a b depth]
 ([[:vector . xs] [`every? p '%] d]
  (l/project [xs] (every-sub xs p d))))
(reg-psub vector-as-every)

; Rules: maps & structural

; Clojure core functions

(set-type! #'+ (l/fne [_] ([[:fn [`int? `int?] `int?]]) ([[:fn [`number? `number?] `number?]])))
(set-type! #'/ (l/fne [_] ([[:fn [`number?] `number?]]) ([[:fn [`number? `number?] `number?]])))
(set-type! #'inc (l/fne [_] ([[:fn [`int?] `int?]])))

(set-type! #'identity (l/fne [_] ([[:fn [a] a]])))
(set-type! #'constantly (l/fne [_] ([[:fn [a] [:fn [_] a]]])))

(set-type! #'map (l/fne [_] ([[:fn [[:fn [a] b] [`every? a '%]] [`every? b '%]]])))
(set-type! #'first (l/fne [_] ([[:fn [[`every? a '%]] a]]) ([[:fn [[:vector a . _]] a]])))
(set-type! #'second (l/fne [_] ([[:fn [[:vector _ . a . _]] a]])))
(set-type! #'rest (l/fne [_] ([[:fn [[`every? a '%]] [`every? a '%]]])))

(comment
  ; Ideally, the syntax would be something along the lines of:
  (forall [a b] `(fn [(every? a %) (fn [a] b)] (every? b %))))
