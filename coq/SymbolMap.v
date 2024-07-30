From SE Require Import SMT.

(* TODO: why is it needed? *)
Set Default Goal Selector "!".

Definition total_map (A : Type) := symbol -> A.

Definition empty_map {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition update_map {A : Type} (m : total_map A) (x : symbol) (v : A) :=
  fun y => if symbol_eqb x y then v else m y.

Notation "'_' '!->' v" := (empty_map v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (update_map m x v)
                              (at level 100, v at next level, right associativity).

Lemma apply_empty_map : forall (A : Type) (x : symbol) (v : A),
  (_ !-> v) x = v.
Proof.
  intros A x v.
  reflexivity.
Qed.

Lemma update_map_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold update_map.
  rewrite symbol_eqb_refl.
  reflexivity.
Qed.

Theorem update_map_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold update_map.
  apply symbol_eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Lemma update_map_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
Admitted.

Theorem update_map_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
Admitted.

Theorem update_map_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
  x2 <> x1 -> (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
Admitted.
