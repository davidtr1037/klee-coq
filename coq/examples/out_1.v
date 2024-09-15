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

Definition inst_0 : llvm_cmd := (CMD_Inst 0 (INSTR_Op (Name "add"%string) (OP_IBinop (LLVMAst.Add false false) (TYPE_I 32) (EXP_Integer (1)%Z) (EXP_Integer (2)%Z)))).

Definition inst_1 : llvm_cmd := (CMD_Inst 1 (INSTR_Op (Name "add1"%string) (OP_IBinop (LLVMAst.Add false false) (TYPE_I 32) (EXP_Ident (ID_Local (Name "add"%string))) (EXP_Integer (7)%Z)))).

Definition inst_2 : llvm_cmd := (CMD_Term 2 (TERM_Ret ((TYPE_I 32), (EXP_Ident (ID_Local (Name "add1"%string)))))).

Definition bb_0 : llvm_block := (mk_block (Name "entry"%string) [inst_0; inst_1; inst_2] None).

Definition decl_main : llvm_declaration := (mk_declaration (Name "main"%string) (TYPE_Function (TYPE_I 32) [] false) ([], [[]; []]) [] []).

Definition def_main : llvm_definition := (mk_definition _ decl_main [] (mk_cfg (Name "entry"%string) [bb_0])).

Definition mdl : llvm_module := (mk_module None None None [] [] [] [def_main]).

Lemma is_supported_inst_0 : (is_supported_cmd inst_0).
Proof.
{
  apply IS_INSTR_Op.
  apply IS_OP_IBinop.
  {
    apply IS_EXP_Integer.
  }
  {
    apply IS_EXP_Integer.
  }
  {
    apply IS_Add.
  }
}
Qed.

Lemma is_supported_inst_1 : (is_supported_cmd inst_1).
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

Lemma is_supported_inst_2 : (is_supported_cmd inst_2).
Proof.
{
  apply IS_Term_Ret.
  {
    apply IS_EXP_Ident.
  }
}
Qed.

Lemma is_supported_bb_0 : (is_supported_block (mk_block (Name "entry"%string) [inst_0; inst_1; inst_2] None)).
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

Definition s_0 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 0) inst_0 [inst_1; inst_2] None (empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_1 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 1) inst_1 [inst_2] None ((Name "add"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_2 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 2) inst_2 [] None ((Name "add1"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); (Name "add"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition t_2 : execution_tree := (t_leaf s_2).

Definition t_1 : execution_tree := (t_subtree s_1 [t_2]).

Definition t_0 : execution_tree := (t_subtree s_0 [t_1]).

Lemma L_2 : (safe_et_opt t_2).
Proof.
apply Safe_Leaf_Ret.
Qed.

Lemma L_1 : (safe_et_opt t_1).
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

Lemma L_0 : (safe_et_opt t_0).
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

