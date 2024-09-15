From Coq Require Import ZArith.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.
From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import ExecutionTreeOpt.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import ProofGeneration.
From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.
From SE.Utils Require Import Util.
Definition gs : smt_store := empty_smt_store.

Definition inst_0 : llvm_cmd := (CMD_Term 0 (TERM_UnconditionalBr (Name "while.cond"%string))).

Definition inst_1 : llvm_cmd := (CMD_Phi 1 (Phi (Name "n.0"%string) (TYPE_I 32) [((Name "entry"%string), (EXP_Integer (0)%Z)); ((Name "while.body"%string), (EXP_Ident (ID_Local (Name "inc"%string))))])).

Definition inst_2 : llvm_cmd := (CMD_Inst 2 (INSTR_Op (Name "cmp"%string) (OP_ICmp Slt (TYPE_I 32) (EXP_Ident (ID_Local (Name "n.0"%string))) (EXP_Integer (2)%Z)))).

Definition inst_3 : llvm_cmd := (CMD_Term 3 (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "cmp"%string)))) (Name "while.body"%string) (Name "while.end"%string))).

Definition inst_4 : llvm_cmd := (CMD_Inst 4 (INSTR_Op (Name "inc"%string) (OP_IBinop (LLVMAst.Add false false) (TYPE_I 32) (EXP_Ident (ID_Local (Name "n.0"%string))) (EXP_Integer (1)%Z)))).

Definition inst_5 : llvm_cmd := (CMD_Term 5 (TERM_UnconditionalBr (Name "while.cond"%string))).

Definition inst_6 : llvm_cmd := (CMD_Term 6 (TERM_Ret ((TYPE_I 32), (EXP_Integer (0)%Z)))).

Definition bb_0 : llvm_block := (mk_block (Name "entry"%string) [inst_0] None).

Definition bb_1 : llvm_block := (mk_block (Name "while.cond"%string) [inst_1; inst_2; inst_3] None).

Definition bb_2 : llvm_block := (mk_block (Name "while.body"%string) [inst_4; inst_5] None).

Definition bb_3 : llvm_block := (mk_block (Name "while.end"%string) [inst_6] None).

Definition decl_main : llvm_declaration := (mk_declaration (Name "main"%string) (TYPE_Function (TYPE_I 32) [] false) ([], [[]; []]) [] []).

Definition def_main : llvm_definition := (mk_definition _ decl_main [] (mk_cfg (Name "entry"%string) [bb_0; bb_1; bb_2; bb_3])).

Definition mdl : llvm_module := (mk_module None None None [] [] [] [def_main]).

Lemma is_supported_inst_0 : (is_supported_cmd inst_0).
Proof.
{
  apply IS_Term_UnconditionalBr.
}
Qed.

Lemma is_supported_inst_1 : (is_supported_cmd inst_1).
Proof.
{
  apply IS_Phi.
  intros bid e Hin.
  destruct Hin as [Hin | Hin].
  {
    inversion Hin.
    subst.
    {
      apply IS_EXP_Integer.
    }
  }
  destruct Hin as [Hin | Hin].
  {
    inversion Hin.
    subst.
    {
      apply IS_EXP_Ident.
    }
  }
  destruct Hin.
}
Qed.

Lemma is_supported_inst_2 : (is_supported_cmd inst_2).
Proof.
{
  apply IS_INSTR_Op.
  apply IS_OP_ICmp.
  {
    apply IS_EXP_Ident.
  }
  {
    apply IS_EXP_Integer.
  }
}
Qed.

Lemma is_supported_inst_3 : (is_supported_cmd inst_3).
Proof.
{
  apply IS_Term_Br.
  {
    apply IS_EXP_Ident.
  }
}
Qed.

Lemma is_supported_inst_4 : (is_supported_cmd inst_4).
Proof.
{
  apply IS_INSTR_Op.
  apply IS_OP_IBinop.
  {
    apply IS_EXP_Ident.
  }
  {
    apply IS_EXP_Integer.
  }
  {
    apply IS_Add.
  }
}
Qed.

Lemma is_supported_inst_5 : (is_supported_cmd inst_5).
Proof.
{
  apply IS_Term_UnconditionalBr.
}
Qed.

Lemma is_supported_inst_6 : (is_supported_cmd inst_6).
Proof.
{
  apply IS_Term_Ret.
  {
    apply IS_EXP_Integer.
  }
}
Qed.

Lemma is_supported_bb_0 : (is_supported_block (mk_block (Name "entry"%string) [inst_0] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_0.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_1 : (is_supported_block (mk_block (Name "while.cond"%string) [inst_1; inst_2; inst_3] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_1.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_2.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_3.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_2 : (is_supported_block (mk_block (Name "while.body"%string) [inst_4; inst_5] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_4.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_5.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_3 : (is_supported_block (mk_block (Name "while.end"%string) [inst_6] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_6.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_def_main : (is_supported_definition def_main).
Proof.
{
  apply IS_Definition.
  intros b Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_0.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_1.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_2.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_3.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_mdl : (is_supported_module mdl).
Proof.
{
  apply IS_Module.
  {
    intros g H.
    destruct H.
  }
  {
    intros d Hin.
    destruct Hin as [Hin | Hin].
    {
      subst.
      apply is_supported_def_main.
    }
    {
      destruct Hin.
    }
  }
}
Qed.

Definition s_0 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 0) inst_0 [] None (empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_1 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "entry"%string)) (empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_2 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "entry"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_3 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "entry"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_4 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_5 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_6 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_7 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_8 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_9 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_10 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_11 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_12 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_13 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 0)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_14 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.end"%string) 6) inst_6 [] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 0)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition t_14 : execution_tree := (t_leaf s_14).

Definition t_13 : execution_tree := (t_subtree s_13 [t_14]).

Definition t_12 : execution_tree := (t_subtree s_12 [t_13]).

Definition t_11 : execution_tree := (t_subtree s_11 [t_12]).

Definition t_10 : execution_tree := (t_subtree s_10 [t_11]).

Definition t_9 : execution_tree := (t_subtree s_9 [t_10]).

Definition t_8 : execution_tree := (t_subtree s_8 [t_9]).

Definition t_7 : execution_tree := (t_subtree s_7 [t_8]).

Definition t_6 : execution_tree := (t_subtree s_6 [t_7]).

Definition t_5 : execution_tree := (t_subtree s_5 [t_6]).

Definition t_4 : execution_tree := (t_subtree s_4 [t_5]).

Definition t_3 : execution_tree := (t_subtree s_3 [t_4]).

Definition t_2 : execution_tree := (t_subtree s_2 [t_3]).

Definition t_1 : execution_tree := (t_subtree s_1 [t_2]).

Definition t_0 : execution_tree := (t_subtree s_0 [t_1]).

Lemma UNSAT_2 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_1 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_0 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma L_14 : (safe_et_opt t_14).
Proof.
apply Safe_Leaf_Ret.
Qed.

Lemma L_13 : (safe_et_opt t_13).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_2.
      }
    }
    {
      left.
      exists (t_14).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_14.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_12 : (safe_et_opt t_12).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_13).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_13.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_11 : (safe_et_opt t_11).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_12).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_12.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_10 : (safe_et_opt t_10).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_11).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_11.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_9 : (safe_et_opt t_9).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_10).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_10.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_8 : (safe_et_opt t_8).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_9).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_9.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_1.
      }
    }
  }
}
Qed.

Lemma L_7 : (safe_et_opt t_7).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_8).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_8.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_6 : (safe_et_opt t_6).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_7).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_7.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_5 : (safe_et_opt t_5).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_6).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_6.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_4 : (safe_et_opt t_4).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
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
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_update (_) (_) (_) (_) (_) (H13)).
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_3 : (safe_et_opt t_3).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
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
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_0.
      }
    }
  }
}
Qed.

Lemma L_2 : (safe_et_opt t_2).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
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
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_update (_) (_) (_) (_) (_) (H13)).
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_1 : (safe_et_opt t_1).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
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
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            inversion H14.
            subst.
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_0 : (safe_et_opt t_0).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
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
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma program_safety : (is_safe_program mdl (Name "main"%string)).
Proof.
{
  destruct t_0 as [r | r l] eqn:E.
  {
    discriminate E.
  }
  {
    apply (completeness_via_et (mdl) ((Name "main"%string)) (s_0) (l)).
    {
      apply is_supported_mdl.
    }
    {
      reflexivity.
    }
    {
      inversion E.
      subst.
      rewrite <- E.
      apply L_0.
    }
  }
}
Qed.

