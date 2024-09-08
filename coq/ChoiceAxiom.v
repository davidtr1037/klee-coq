From Coq Require Import List.
From Coq Require Import String.

Import ListNotations.

(* TODO: use a more readable: fresh_name (n : nat) / extend_names (n : nat) *)

Definition fresh_name (l : list string) : string.
Admitted.

Definition extend_names (l : list string) : list string :=
  (fresh_name l) :: l.

Lemma fresh_name_lemma : forall l, ~ In (fresh_name l) l.
Proof.
Admitted.
