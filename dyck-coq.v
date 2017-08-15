(* Some basics. *)

(* Some theorems about the Dyck language in Coq. *)
Require Import Arith.
Require Import Omega.
Require Import Lists.List.
Require Import Coq.Arith.Even.

(* Some simple notations. *)
Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " x :: y " := (cons x y).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).
Infix "==n" := beq_nat (no associativity, at level 50).

Inductive paren := open | close.

(*
Notation " ( " := open (at level 200).
Notation " ) " := close (at level 200).
*)

Definition String := list paren.

Inductive InDyck : String -> Prop :=
| InDyckEpsilon : InDyck nil
| InDyckSplit u v (_ : InDyck u) (_ : InDyck v) :
    InDyck ([ open ] ++ u ++ [ close ] ++ v).

Theorem dyck_strings_have_even_length :
  forall s, InDyck s -> even (length s).
Proof.
  intros.
  induction H; simpl; constructor.
  {
    rewrite app_length.
    simpl.
    rewrite NPeano.Nat.add_succ_r.
    repeat constructor.
    apply even_even_plus; assumption.
  }
Qed.

Definition beq_paren a b :=
  match a, b with
    | open, open => true
    | open, close => false
    | close, open => false
    | close, close => true
  end.

Theorem eq_paren_dec : forall a b : paren, {a = b} + {a <> b}.
Proof.
  intros.
  destruct a; destruct b.
  left; constructor.
  right; discriminate.
  right; discriminate.
  left; constructor.
Defined.

Compute (count_occ eq_paren_dec [ open ; open ; close ] open).

Lemma count_occ_app :
  forall T H (a : T) l1 l2, count_occ H (l1 ++ l2) a = count_occ H l1 a + count_occ H l2 a.
Proof.
  intros.
  induction l1.
  firstorder.
  simpl.
  destruct (H a0 a).
  rewrite IHl1.
  omega.
  assumption.
Qed.

Theorem dyck_equal_counts :
  forall s, InDyck s -> count_occ eq_paren_dec s open = count_occ eq_paren_dec s close.
Proof.
  intros.
  induction H.
  { reflexivity. }
  {
    simpl.
    destruct u.
    {
      simpl.
      firstorder.
    }
    {
      repeat rewrite count_occ_app.
      rewrite IHInDyck1.
      simpl.
      rewrite IHInDyck2.
      omega.
    }
  }
Qed.

(* Give decidability. *)

Fixpoint dyck_checker_helper count s : bool :=
  match s with
    | nil => count ==n 0
    | open :: s' => dyck_checker_helper (S count) s'
    | close :: s' =>
      match count with
        | 0 => false
        | S count' => dyck_checker_helper count' s'
      end
  end.

Definition dyck_checker := dyck_checker_helper 0.

(* We will now work towards proving that dyck_checker is good. *)

Fixpoint 

( ( ) ( ) )

Fixpoint extract_dyck_atom count s accum : String * String :=
  match s with
  | [] => ([], [])
  | 
  end.

Theorem dyck_checker_good :
  forall s, if dyck_checker s then InDyck s else ~ InDyck s.
Proof.

 ( ( ) ( ) )

Compute (dyck_checker [ { ; { ; } ; { ; } ; } ] 0).

Theorem

Example example1 : InDyck [ { ; { ; } ; { ; } ; } ].
Proof.
  eapply (InDyckSplit _ []).
