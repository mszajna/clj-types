(ns types
  (:require [clojure.core.logic :as l :refer [defne]]
            [clojure.core.logic.protocols :refer [lfirst lnext]]
            [clojure.walk :refer [postwalk]]))

(def
  ^{:doc "clojure.core.logic relation asserting that smaller is a subset of larger."
    :dynamic true
    :arglists '([smaller larger depth])}
  sub)

(defn interruptible [a]
  (when (Thread/interrupted) (throw (new InterruptedException)))
  a)

(defn log-sub [a b]
  (fn [x]
    (letfn [(get-var [v] (let [val (l/-reify x v)] (if (seqable? val) (doall val) val)))]
      (println "sub: left =" (get-var a))
      (println "    right =" (get-var b)))
    x))

(defn make-sub [sub-rules]
  (let [reg-sub
        (l/fne [a b depth]
          ([a b d]
            interruptible
            (log-sub a b)
            (l/or* (map #(% a b d) sub-rules))))]
    
    (l/fne [a b depth] :tabled
      ([x x _])
      ([[ctr . _] [ctr . _] [_ . d]] (reg-sub a b d))
      ([x y [_ . d]] (reg-sub a b d))
      ([x z [_ . d]] (l/fresh [y] (reg-sub x y [0]) (sub y z d))))))
    ; (l/fne [a b depth] :tabled
    ;   ([x x _])
    ;   ([x y [_ . d]] (reg-sub x y d))
    ;   ([x z [_ . d]] (l/fresh [y] (reg-sub x y [0]) (sub y z d))))))

(defn with-rules* [sub-rules f]
  (binding [sub (make-sub sub-rules)]
    (f)))

; Declaring global rules

(def global-sub-rules (atom []))
(defn rule! [r] (swap! global-sub-rules conj r))

(defmacro with-regs [& body]
 `(with-rules* @global-sub-rules #(do ~@body)))

; Assigning types to vars

(defn set-type! [var type]
  (alter-meta! var assoc :type type))

(defn get-var-type [qsym]
  (-> qsym resolve meta :type))

; Function application relation:

(defne app [f args e depth]
  ([[:fn [a] r] [p] r d] (sub p a d))
  ([[:fn [a1 a2] r] [p1 p2] r d] (sub p1 a1 d) (sub p2 a2 d))
  ([[:fn [a1 a2 a3] r] [p1 p2 p3] r d] (sub p1 a1 d) (sub p2 a2 d) (sub p3 a3 d)))
; TODO: more arities

; ##### 'type' macro ######
; #########################

(defn var-name [env sym]
  (when-let [v (and (symbol? sym) (resolve env sym))]
    (let [nm (:name (meta v))
          nsp (.getName ^clojure.lang.Namespace (:ns (meta v)))]
      (symbol (name nsp) (name nm)))))

(defn teval [env x result depth]
  (let [call (when (seq? x) (first x))]
    (cond
      (or (number? x) (string? x) (keyword? x))
     `(l/== ~result [:lit ~x])

      (= 'fn call)
      (let [[_ args & body] x ; TODO: expand support to multi-arities
            nenv (gensym "nenv")
            r (gensym "r")]
       `(l/fresh [~@args ~r]
          (l/== ~result (list :fn [~@args] ~r))
         ~(teval (merge env (zipmap args (repeat true))) `(do ~@body) r depth)))
      
      (= 'do call)
      (let [xs (rest x)]
        (cond
          (empty? xs) `(l/== ~result nil)
          (empty? (rest xs)) (teval env (first xs) result depth)
          :else
          (let [syms (mapv (fn [_] (gensym "_")) (butlast xs))]
           `(l/fresh ~syms
             ~@(map #(teval env %1 %2 depth) (butlast xs) syms)
             ~(teval env (last xs) result depth)))))

      (seq? x)
      (let [f (gensym "f")
            syms (mapv (fn [_] (gensym "e")) (rest x))]
       `(l/fresh [~f ~@syms]
         ~@(map #(teval env %1 %2 depth) (rest x) syms)
          (app ~f ~syms ~result ~depth)
         ~(teval env (first x) f depth)
         ))

      (vector? x)
      (let [syms (mapv (fn [_] (gensym "e")) x)]
       `(l/fresh [~@syms]
         ~@(map #(teval env %1 %2 depth) x syms)
          (l/== ~result [:vec ~@syms])))

      (map? x)
      (let [key+syms (mapv (fn [[k v]] [v (gensym "e") k]) x)]
       `(l/fresh [~@(map second key+syms)]
         ~@(map #(teval env (first %) (second %) depth) key+syms)
          (l/== ~result [:map ~@(mapcat (fn [[_ s k]] [k s]) key+syms)])))
          ; TODO: this should only work for literal keys

      (symbol? x)
      (if-let [name (var-name env x)]
       `((get-var-type (quote ~name)) ~result)
       `(l/== ~result ~x))

      :else (throw (new IllegalArgumentException (str "wtf is " x))))))

; The following two work around what seems to be a bug in clojure.core.logic,
; where an LCons in return value is sometimes not translated back to Seq.
(defn lcons->seq [v]
  (cond
    (l/lcons? v) (cons (lfirst v) (lcons->seq (lnext v)))
    (symbol? v) (list '. v)
    :else nil))
(defn fix-lcons [v]
  (postwalk (fn [x] (if (l/lcons? x) (lcons->seq x) x)) v))

(defmacro type
 ([exp] `(types/type nil ~exp))
 ([{:keys [n d] :or {n 1 d 3}} exp]
  (let [e (gensym "e")]
   `(with-regs
      (doall
        (map fix-lcons
          (l/run ~n [~e]
          ~(teval &env exp e `(range ~d)))))))))

; ######## RULES ########################
; #######################################

; Rules: numbers

; (defne literalo [x]
;   ([x] (l/pred x number?))
;   ([x] (l/pred x keyword?))
;   ([x] (l/pred x string?)))

; (defn literal? [x]
;   (or (number? x) (keyword? x) (string? x)))

; (defne literals [a b _] ([x [:lit x] _] (l/pred x literal?)))
; (rule! literals)

(defne int-literal [a b _] ([[:lit x] `int? _] (l/pred x int?)))
(rule! int-literal)

(defne int-is-num [a b _] ([`int? `number? _]))
(rule! int-is-num)

(defne float-literal [a b _] ([[:lit x] `float? _] (l/pred x float?)))
(rule! float-literal)

(defne float-is-num [a b _] ([`float? `number? _]))
(rule! float-is-num)

(defne ratio-literal [a b _] ([[:lit x] `ratio? _] (l/pred x ratio?)))
(rule! ratio-literal)

(defne ratio-is-num [a b _] ([`ratio? `number? _]))
(rule! ratio-is-num)

; Rules: functions

(defne sub-args [a b depth max-args]
 ([[] [] _ _])
 ([['& xs] ['& ys] d _] (sub xs ys d))
 ([[x . xs] [y . ys] d [_ . a]]
  (sub y x d)
  (sub-args xs ys d a)))
; TODO: (= [:fn [`int? & `int?] `int?]  [:fn [& `int?] `int?])

(def max-args 20) ; maximum number of arguments supported by Clojure functions

(defne function-n-arity [a b depth]
 ([[:fn largs lr . nil] [:fn rargs rr . nil] d]
  (sub-args largs rargs d (range max-args))
  (sub lr rr d)))
(rule! function-n-arity)

; Rules: lists

(defne homogeneous-collection [a b depth]
 ([[`every? x '% . nil] [`every? y '% . nil] d] (sub x y d)))
(rule! homogeneous-collection)

; Rules: vectors / tuples

(defne every-sub [coll pred depth]
 ([[] _ d])
 ([[x . xs] p d]
  (sub x p d)
  (every-sub xs p d)))

(defn vector-as-every [a b depth]
  (l/pred a vector?)
  (l/matche [b]
   ([[`every? p '% . nil]] (every-sub a p depth))))
(rule! vector-as-every)

; Rules: maps & structural

; Operations below apply to a map as vector of [k1 v1 kv v2 ...]
(l/defne assoco [input-map key val output-map]
  ([[k _ . kv] k v [k v . kv]])
  ([() k v [k v . nil]])
  ([[k1 v1 . m1] k v [k1 v1 . m2]]
    (l/!= k1 k)
    (assoco m1 k v m2)))

(l/defne geto [map key value]
  ([[k v . _] k v])
  ; If I remove this rule I can force the map to contain the expected value, which is in
  ; many cases what you'd want.
  ([() _ nil]) 
  ([[nk _ . m] k v] (l/!= nk k) (geto m k v)))

(defn every-kv? [m kpred vpred]
  (and (every? kpred (keys m)) (every? vpred (vals m))))

(defne every-kvo [map kp vp depth]
  ([[] _ _ _])
  ([[k v . m] kp vp [_ . d]]
    (sub k kp d)
    (sub v vp d)
    (every-kvo m kp vp d)))

(defne map-as-every-kv [a b depth]
  ([[:map . m] [`every-kv? kp vp] d] (every-kvo m kp vp d)))
(rule! map-as-every-kv)

(defne homogeneous-map [a b depth]
 ([[`every-kv? lk lv] [`every-kv? rk rv] [_ . d]]
  (sub rk lk d)
  (sub lv rv d)))
(rule! homogeneous-map)

; Nullability
; TODO: ideally this would be expressed as union type

; Clojure core functions

(set-type! #'+ (l/fne [_] ([[:fn [`int? `int?] `int? . nil]])
                          ([[:fn [`number? `number?] `number? . nil]])))
(set-type! #'/ (l/fne [_] ([[:fn [`number?] `number? . nil]])
                          ([[:fn [`number? `number?] `number? . nil]])))
(set-type! #'inc (l/fne [_] ([[:fn [`int?] `int? . nil]])))

(set-type! #'identity (l/fne [_] ([[:fn [a] a . nil]])))
(set-type! #'constantly (l/fne [_] ([[:fn [a] [:fn [_] a . nil] . nil]])))

(set-type! #'map (l/fne [_] ([[:fn [[:fn [a] b . nil] [`every? a '% . nil]] [`every? b '% . nil] . nil]])))
(set-type! #'first (l/fne [_] ([[:fn [[`every? a '% . nil]] a . nil]])))
(set-type! #'rest (l/fne [_] ([[:fn [[`every? a '% . nil]] [`every? a '% . nil] . nil]])))

(set-type! #'assoc (l/fne [_] ([[:fn [[:map . m1] [:lit k] v] [:map . m2] . nil]] (assoco m1 k v m2))
                             )); ([[:fn [[`every-kv? k v] k v] [`every-kv? k v]]])))
(set-type! #'get (l/fne [_] ([[:fn [[:map . m] [:lit k]] v . nil]] (geto m k v))
                           )); ([[:fn [[`every-kv? k v . nil] k] [:or v nil] . nil]])))