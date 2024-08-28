From Coq Require Import ZArith.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.
From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import ExecutionTreeOpt.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Symbolic.
From SE Require Import ProofGeneration.
From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.
Definition inst_0 : llvm_cmd :=
  (CMD_Inst
    0
    (INSTR_Op
      (Name
        "cmp"%string
      )
      (OP_ICmp
        Sgt
        (TYPE_I
          32
        )
        (EXP_Integer
          (10)%Z
        )
        (EXP_Integer
          (7)%Z
        )
      )
    )
  ).

Definition inst_1 : llvm_cmd :=
  (CMD_Term
    1
    (TERM_Br
      (
        (TYPE_I
          1
        ),
        (EXP_Ident
          (ID_Local
            (Name
              "cmp"%string
            )
          )
        )
      )
      (Name
        "if.then"%string
      )
      (Name
        "if.end"%string
      )
    )
  ).

Definition inst_2 : llvm_cmd :=
  (CMD_Inst
    2
    (INSTR_Op
      (Name
        "inc"%string
      )
      (OP_IBinop
        (LLVMAst.Add
          false
          false
        )
        (TYPE_I
          32
        )
        (EXP_Integer
          (0)%Z
        )
        (EXP_Integer
          (1)%Z
        )
      )
    )
  ).

Definition inst_3 : llvm_cmd :=
  (CMD_Term
    3
    (TERM_UnconditionalBr
      (Name
        "if.end"%string
      )
    )
  ).

Definition inst_4 : llvm_cmd :=
  (CMD_Phi
    4
    (Phi
      (Name
        "y.0"%string
      )
      (TYPE_I
        32
      )
      [
        (
          (Name
            "if.then"%string
          ),
          (EXP_Ident
            (ID_Local
              (Name
                "inc"%string
              )
            )
          )
        );
        (
          (Name
            "entry"%string
          ),
          (EXP_Integer
            (0)%Z
          )
        )
      ]
    )
  ).

Definition inst_5 : llvm_cmd :=
  (CMD_Term
    5
    (TERM_Ret
      (
        (TYPE_I
          32
        ),
        (EXP_Ident
          (ID_Local
            (Name
              "y.0"%string
            )
          )
        )
      )
    )
  ).

Definition bb_0 : llvm_block :=
  (mk_block
    (Name
      "entry"%string
    )
    [
      inst_0;
      inst_1
    ]
    None
  ).

Definition bb_1 : llvm_block :=
  (mk_block
    (Name
      "if.then"%string
    )
    [
      inst_2;
      inst_3
    ]
    None
  ).

Definition bb_2 : llvm_block :=
  (mk_block
    (Name
      "if.end"%string
    )
    [
      inst_4;
      inst_5
    ]
    None
  ).

Definition def_0 : llvm_definition :=
  (mk_definition
    _
    (mk_declaration
      (Name
        "main"%string
      )
      (TYPE_Function
        (TYPE_I
          32
        )
        []
        false
      )
      (
        [],
        [
          [];
          []
        ]
      )
      []
      []
    )
    []
    (mk_cfg
      (Name
        "entry"%string
      )
      [
        bb_0;
        bb_1;
        bb_2
      ]
    )
  ).

Definition mdl : llvm_module :=
  (mk_module
    None
    None
    None
    []
    []
    []
    [
      def_0
    ]
  ).

Definition gs := empty_smt_store.

Definition s_ls_0 := empty_smt_store.
Definition s_symbolics_0 : list string := [].
Definition s_pc_0 := SMT_True.
Definition s_0 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 0)
  inst_0
  [inst_1]
  None
  s_ls_0
  []
  gs
  s_symbolics_0
  s_pc_0
  mdl
.

Definition s_ls_1 := ((Name "cmp") !-> Some (SMT_Const_I1 one); s_ls_0).
Definition s_symbolics_1 : list string := [].
Definition s_pc_1 := SMT_True.
Definition s_1 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 1)
  inst_1
  []
  None
  s_ls_1
  []
  gs
  s_symbolics_1
  s_pc_1
  mdl
.

Definition s_ls_2 := s_ls_1.
Definition s_symbolics_2 : list string := [].
Definition s_pc_2 := SMT_True.
Definition s_2 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "if.then") 2)
  inst_2
  [inst_3]
  (Some (Name "entry"))
  s_ls_2
  []
  gs
  s_symbolics_2
  s_pc_2
  mdl
.

Definition s_ls_3 := ((Name "inc") !-> Some (SMT_Const_I32 (Int32.repr 1)); s_ls_2).
Definition s_symbolics_3 : list string := [].
Definition s_pc_3 := SMT_True.
Definition s_3 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "if.then") 3)
  inst_3
  []
  (Some (Name "entry"))
  s_ls_3
  []
  gs
  s_symbolics_3
  s_pc_3
  mdl
.

Definition s_ls_4 := s_ls_3.
Definition s_symbolics_4 : list string := [].
Definition s_pc_4 := SMT_True.
Definition s_4 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "if.end") 4)
  inst_4
  [inst_5]
  (Some (Name "if.then"))
  s_ls_4
  []
  gs
  s_symbolics_4
  s_pc_4
  mdl
.

Definition s_ls_5 := ((Name "y.0") !-> Some (SMT_Const_I32 (Int32.repr 1)); s_ls_4).
Definition s_symbolics_5 : list string := [].
Definition s_pc_5 := SMT_True.
Definition s_5 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "if.end") 5)
  inst_5
  []
  (Some (Name "if.then"))
  s_ls_5
  []
  gs
  s_symbolics_5
  s_pc_5
  mdl
.

(* unsat *)
Definition s_ls_6 := s_ls_1.
Definition s_symbolics_6 : list string := [].
Definition s_pc_6 := SMT_False.
Definition s_6 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "if.end") 4)
  inst_4
  [inst_5]
  (Some (Name "entry"))
  s_ls_6
  []
  gs
  s_symbolics_6
  s_pc_6
  mdl
.

Definition t_6 := t_leaf s_6.
Definition t_5 := t_leaf s_5.
Definition t_4 := t_subtree s_4 [t_5].
Definition t_3 := t_subtree s_3 [t_4].
Definition t_2 := t_subtree s_2 [t_3].
Definition t_1 := t_subtree s_1 [t_2; t_6].
Definition t_0 := t_subtree s_0 [t_1].

Lemma L_5 : safe_et_opt t_5.
Proof.
apply Safe_Leaf_Ret.
Qed.

Lemma L_4 : safe_et_opt t_4.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_phi.
  }
  {
    intros s Hse.
    {
      left.
      exists (t_5).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_5.
        }
        {
          simpl.
          inversion Hse; subst.
          apply EquivSymState.
          {
            simpl in H14.
            (* TODO: avoid *)
            inversion H14; subst.
            apply equiv_smt_store_refl.
          }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Qed.

Lemma L_3 : safe_et_opt t_3.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_unconditional_br.
  }
  {
    intros s Hse.
    {
      left.
      exists (t_4).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_4.
        }
        {
          simpl.
          inversion Hse; subst.
          (* TODO use a specific lemma *)
          inversion H10; subst.
          inversion H11; subst.
          inversion H12; subst.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Qed.

Lemma L_2 : safe_et_opt t_2.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_instr_op.
  }
  {
    intros s Hse.
    {
      left.
      exists (t_3).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_3.
        }
        {
          simpl.
          inversion Hse; subst.
          apply EquivSymState.
          {
            simpl in H13.
            apply LAUX_1 with
              (se1 := (SMT_BinOp SMT_Add (SMT_Const_I32 (Int32.repr 0)) (SMT_Const_I32 (Int32.repr 1))))
              (se2 := se).
            { assumption. }
            { admit. } (* simplify lemma *)
          }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Admitted.

Lemma L_1 : safe_et_opt t_1.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_br.
  }
  {
    intros s Hse.
    inversion Hse; subst.
    {
      left.
      exists (t_2).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_2.
        }
        {
          simpl.
          inversion H13; subst.
          inversion H14; subst.
          inversion H15; subst.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          {
            inversion H12; subst.
            (* TODO: simplify lemma *)
            admit.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12; subst.
      (* TODO: add axiom *)
      admit.
    }
  }
}
Admitted.

Lemma L_0 : safe_et_opt t_0.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_instr_op.
  }
  {
    intros s Hse.
    {
      left.
      exists (t_1).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_1.
        }
        {
          simpl.
          inversion Hse; subst.
          apply EquivSymState.
          {
            simpl in H13.
            apply LAUX_1 with
              (se1 := (sym_eval_icmp Sgt (SMT_Const_I32 (Int32.repr 10)) (SMT_Const_I32 (Int32.repr 7))))
              (se2 := se).
            { assumption. }
            { admit. } (* simplify lemma *)
          }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Admitted.

Theorem program_safe : is_safe_program mdl (Name "main").
Proof.
{
  destruct t_0 as [r | r l] eqn:E.
  {
    discriminate E.
  }
  {
    apply completeness_via_et with (init_s := s_0) (l := l).
    { admit. }
    { reflexivity. }
    {
      inversion E; subst.
      rewrite <- E.
      apply L_0.
    }
  }
}
Admitted.
