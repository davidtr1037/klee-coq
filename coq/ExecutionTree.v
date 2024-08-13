From Coq Require Import List.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Completeness.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Module.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

Inductive tree (X : Type) : Type :=
  | t_leaf (x : X)
  | t_subtree (x : X) (l : list (tree X))
.

Arguments t_leaf {X}.
Arguments t_subtree {X}.

Definition root {X : Type} (t : tree X) : X :=
  match t with
  | t_leaf x => x
  | t_subtree x _ => x
  end
.

Arguments root {X}.

Definition execution_tree := tree sym_state.

Inductive safe_et : execution_tree -> Prop :=
  | Safe_Leaf_RetVoid: forall ic cid pbid ls gs syms pc mdl,
      safe_et
        (t_leaf
          (mk_sym_state
            ic
            (CMD_Term cid TERM_RetVoid)
            []
            pbid
            ls
            []
            gs
            syms
            pc
            mdl
          )
        )
  | Safe_Leaf_Ret: forall ic cid t e pbid ls gs syms pc mdl,
      safe_et
        (t_leaf
          (mk_sym_state
            ic
            (CMD_Term cid (TERM_Ret (t, e)))
            []
            pbid
            ls
            []
            gs
            syms
            pc
            mdl
          )
        )
  | Safe_Subtree: forall s l,
      ~ error_sym_state s-> (* to avoid an error state with no children *)
      (forall s',
        sym_step s s' ->
        (
          (exists t, (In t l /\ safe_et t /\ s' = root t)) \/ 
          (unsat_sym_state s')
        )
      ) -> safe_et (t_subtree s l)
.

Lemma safe_leaf: forall s,
  safe_et (t_leaf s) -> ~ error_sym_state s.
Proof.
Admitted.

Lemma safe_subtree: forall s l,
  safe_et (t_subtree s l) -> ~ error_sym_state s.
Proof.
Admitted.

Lemma safe_single_step: forall s s' l,
  safe_et (t_subtree s l) ->
  sym_step s s' ->
  (safe_et (t_leaf s') \/ (exists l', safe_et (t_subtree s' l')) \/ unsat_sym_state s').
Proof.
Admitted.

Lemma safe_multi_step: forall s s' l,
  safe_et (t_subtree s l) ->
  multi_sym_step s s' ->
  (safe_et (t_leaf s') \/ (exists l', safe_et (t_subtree s' l')) \/ unsat_sym_state s').
Proof.
Admitted.

Theorem completeness_via_et: forall mdl d init_s l,
  is_supported_module mdl ->
  (init_sym_state mdl d) = Some init_s ->
  safe_et (t_subtree init_s l) -> 
  is_safe_program mdl d.
Proof.
  intros mdl d init_s l Hism Hinit Hse.
  unfold is_safe_program.
  assert(L0: exists init_c, init_state mdl d = Some init_c).
  { apply (initialization_correspondence mdl d). exists init_s. assumption. }
  destruct L0 as [init_c L0].
  exists init_c.
  split.
  { assumption. }
  {
    intros c Hms.
    assert(L1:
      (exists init_s s,
        (init_sym_state mdl d) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c)
    ).
    { apply completeness with (init_c :=  init_c); assumption. }
    destruct L1 as [init_s' [s [L1_1 [L1_2 L1_3]]]].
    rewrite L1_1 in Hinit.
    inversion Hinit; subst.
    assert(L: safe_et (t_leaf s) \/ (exists l', safe_et (t_subtree s l')) \/ unsat_sym_state s).
    { apply (safe_multi_step init_s s l); assumption. }
    destruct L as [L | [L | L]].
    {
      assert(L2: ~ error_sym_state s).
      { apply safe_leaf. assumption. }
      intros Hes.
      apply error_correspondence in L1_3.
      apply L1_3 in Hes.
      apply L2.
      assumption.
    }
    {
      destruct L as [l' L].
      assert(L3: ~ error_sym_state s).
      { apply safe_subtree with (l := l'). assumption. }
      intros Hes.
      apply error_correspondence in L1_3.
      apply L1_3 in Hes.
      apply L3.
      assumption.
    }
    {
      inversion L1_3; subst.
      destruct H as [m H].
      inversion H; subst.
      destruct H0 as [H0_1 [H0_2 H0_3]].
      inversion L; subst.
      unfold unsat in H1.
      destruct H1.
      unfold sat.
      exists m.
      unfold sat_via.
      assumption.
    }
  }
Qed.
