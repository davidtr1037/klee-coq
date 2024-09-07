From Coq Require Import List.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Completeness.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import ExecutionTreeOpt.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import IDMap.

(* TODO: rename lemmas *)

Lemma LAUX_not_error_instr_op : forall ic cid v e cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v e))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid v e cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma LAUX_not_error_phi : forall ic cid v t args cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Phi cid (Phi v t args))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid v t args cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma LAUX_not_error_unconditional_br : forall ic cid bid cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_UnconditionalBr bid))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid bid cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma LAUX_not_error_br : forall ic cid e bid1 bid2 cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_Br e bid1 bid2))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid e bid1 bid2 cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma LAUX_not_error_call : forall ic cid v f args anns cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Call v f args anns))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid v f args anns cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma LAUX_not_error_void_call : forall ic cid f args anns cs pbid ls stk gs syms pc mdl,
  f <> (TYPE_Void, assert_exp) ->
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_VoidCall f args anns))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid f args anns cs pbid ls stk gs syms pc mdl Hf.
  intros H.
  inversion H; subst.
  apply Hf.
  reflexivity.
Qed.

Lemma LAUX_not_error_ret : forall ic cid e cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_Ret e))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid e cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma LAUX_not_error_ret_void : forall ic cid cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid TERM_RetVoid)
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma LAUX_1 : forall s v se1 se2 se3,
  Some se1 = Some se2 ->
  equiv_smt_expr se1 se3 ->
  equiv_smt_store (v !-> Some se2; s) (v !-> Some se3; s).
Proof.
  intros s v se1 se2 se3 H Heq.
  inversion H; subst.
  apply equiv_smt_store_update.
  { apply equiv_smt_store_refl. }
  { assumption. }
Qed.

Lemma LAUX_2: forall m x se1 se2 se3 l,
  equiv_smt_expr se2 se3 ->
  equiv_smt_store
    (x !-> Some se2; (multi_update_map (x !-> Some se1; m) l))
    (x !-> Some se3; (multi_update_map m l)).
Proof.
  intros m x se1 se2 se3 l Heq.
  apply EquivSMTStore.
  intros y.
  destruct (raw_id_eqb x y) eqn:E.
  {
    apply raw_id_eqb_eq in E.
    rewrite E.
    rewrite update_map_eq, update_map_eq.
    right.
    exists se2, se3.
    split; try reflexivity.
    split; try reflexivity.
    assumption.
  }
  {
    apply raw_id_eqb_neq in E.
    rewrite update_map_neq, update_map_neq; try (assumption).
    assert(L: (multi_update_map (x !-> Some se1; m) l y) = (multi_update_map m l y)).
    {
      apply lemma_multi_update_map_2.
      assumption.
    }
    rewrite L.
    destruct (multi_update_map m l y) as [se | ] eqn:Ey.
    {
      right.
      exists se, se.
      split; try reflexivity.
      split; try reflexivity.
      apply equiv_smt_expr_refl.
    }
    {
      left.
      split; reflexivity.
    }
  }
Qed.

Lemma LAUX_normalize_simplify: forall e,
  equiv_smt_expr e (simplify (normalize e)).
Proof.
Admitted.

Lemma equiv_smt_expr_implied_condition: forall e1 e2,
  unsat (SMT_BinOp SMT_And e1 (SMT_Not e2)) ->
  equiv_smt_expr (SMT_BinOp SMT_And e1 e2) e1.
Proof.
Admitted.

Lemma LAUX_4_1: forall e1 e2 e3,
  equiv_smt_expr (SMT_BinOp SMT_And e1 (SMT_Not e2)) e3 ->
  unsat e3 ->
  equiv_smt_expr (SMT_BinOp SMT_And e1 e2) e1.
Proof.
  intros e1 e2 e3 Heq Hunsat.
  apply equiv_smt_expr_implied_condition.
  apply equiv_smt_expr_unsat with (e1 := e3).
  { apply equiv_smt_expr_symmetry. assumption. }
  { assumption. }
Qed.
