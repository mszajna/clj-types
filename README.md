# clj-types

This is a toy type system for Clojure.

Features:
- inference,
- types decoupled from class hierarchy,
- relationships between types expressed as clojure.core.logic relations.

## Usage

```clojure
(require '[types :as t])

(t/type 1 (fn [a] (map inc a)))
; => ([:fn [[:list :int]] [:list :int]])
```

## Status & limitations

The type checker is highly experimental.

- supports only `fn` abstraction (`let` is not supported yet) and function application,
- very few `clojure.core` functions have been annotated (`+`, `inc`, `identity`, `map`),
- permitted literals are limited to ints,
- failure to type check sometimes manifests as an infinite loop.
