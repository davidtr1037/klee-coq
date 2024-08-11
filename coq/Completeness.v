From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

(* TODO: rename *)
Lemma smt_lemma_1 : forall c_ls s_ls c_gs s_gs ot e m,
    (forall (x : raw_id), equiv_via_model (c_ls x) (s_ls x) m) /\
    (forall (x : raw_id), equiv_via_model (c_gs x) (s_gs x) m) /\
    equiv_via_model (eval_exp c_ls c_gs ot e) (sym_eval_exp s_ls s_gs ot e) m.
Proof.
Admitted.

Lemma completeness_single_step :
  forall c c' s,
    is_supported_state c ->
    step c c' ->
    well_defined s ->
    over_approx s c ->
    (exists s', sym_step s s' /\ over_approx s' c').
Proof.
  intros c c' s Hiss Hs Hwd Hoa.
  destruct c as [c_ic c_c c_cs c_pbid c_ls c_stk c_gs c_mdl].
  destruct s as [s_ic s_c s_cs s_pbid s_ls s_stk s_gs s_syms s_pc s_mdl].
  inversion Hs; subst.
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      equiv_via_model
        (eval_exp c_ls c_gs None e)
        (sym_eval_exp s_ls s_gs None e)
        m
    ).
    { apply smt_lemma_1. }
    inversion L; subst.
    { simpl in H8. rewrite H8 in *. discriminate H1. }
    {
      exists (mk_sym_state
        (next_inst_counter c_ic c)
        c
        cs
        c_pbid
        (v !-> Some se; s_ls)
        s_stk
        s_gs
        s_syms
        s_pc
        c_mdl
      ).
      split.
      {
        apply Sym_Step_OP.
        symmetry.
        simpl.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State.
        destruct H20 as [H20_1 [H20_2 H20_3]].
        split.
        {
          intros x.
          destruct (raw_id_eqb x v) eqn:E.
          {
            rewrite raw_id_eqb_eq in E.
            rewrite E.
            rewrite update_map_eq, update_map_eq.
            rewrite H8 in H0.
            rewrite <- H0.
            apply EVM_Some.
            assumption.
          }
          {
            rewrite raw_id_eqb_neq in E.
            rewrite update_map_neq, update_map_neq; try (symmetry; assumption).
            apply H20_1.
          }
        }
        {
          split.
          { apply H20_2. }
          { assumption. }
        }
      }
    }
  }
Admitted.

(* TODO: add module preconditions *)
Lemma completeness :
  forall (mdl : llvm_module) (d : llvm_definition) (c : state),
    exists init_c,
      (init_state mdl d) = Some init_c ->
      multi_step init_c c ->
      (exists init_s s,
        (init_sym_state mdl d) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c).
Proof.
Admitted.
