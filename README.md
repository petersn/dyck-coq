## Dyck language proofs in Coq.

The Dyck language is the language of strings of balanced parens.
Here we formalize the Dyck language in Coq, and prove some properties about it.

The basic formalization is via the context-free grammar generated by `S -> (S)S | ε`, which is implemented as an inductive in Prop:

```coq
Inductive paren := open | close.
Definition String := list paren.
Inductive InDyck : String -> Prop :=
  | InDyckEpsilon : InDyck nil
  | InDyckSplit u v (_ : InDyck u) (_ : InDyck v) :
      InDyck ([ open ] ++ u ++ [ close ] ++ v).
```
