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

Definition inst_0 : llvm_cmd := (CMD_Inst 0 (INSTR_Call (Name "call"%string) ((TYPE_I 32), (EXP_Ident (ID_Global (Name "klee_make_symbolic_int32"%string)))) [] [])).

Definition inst_1 : llvm_cmd := (CMD_Inst 1 (INSTR_Op (Name "cmp"%string) (OP_ICmp Sgt (TYPE_I 32) (EXP_Ident (ID_Local (Name "call"%string))) (EXP_Integer (7)%Z)))).

Definition inst_2 : llvm_cmd := (CMD_Inst 2 (INSTR_VoidCall (TYPE_Void, (EXP_Ident (ID_Global (Name "klee_assume_bool"%string)))) [(((TYPE_I 1), (EXP_Ident (ID_Local (Name "cmp"%string)))), [])] [])).

Definition inst_3 : llvm_cmd := (CMD_Inst 3 (INSTR_Op (Name "cmp1"%string) (OP_ICmp Sgt (TYPE_I 32) (EXP_Ident (ID_Local (Name "call"%string))) (EXP_Integer (0)%Z)))).

Definition inst_4 : llvm_cmd := (CMD_Term 4 (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "cmp1"%string)))) (Name "if.then"%string) (Name "if.else"%string))).

Definition inst_5 : llvm_cmd := (CMD_Term 5 (TERM_UnconditionalBr (Name "if.end"%string))).

Definition inst_7 : llvm_cmd := (CMD_Term 7 TERM_Unreachable).

Definition inst_8 : llvm_cmd := (CMD_Inst 8 (INSTR_Op (Name "cmp2"%string) (OP_ICmp Slt (TYPE_I 32) (EXP_Ident (ID_Local (Name "call"%string))) (EXP_Integer (3)%Z)))).

Definition inst_9 : llvm_cmd := (CMD_Term 9 (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "cmp2"%string)))) (Name "if.then3"%string) (Name "if.else4"%string))).

Definition inst_10 : llvm_cmd := (CMD_Term 10 (TERM_UnconditionalBr (Name "return"%string))).

Definition inst_11 : llvm_cmd := (CMD_Term 11 (TERM_UnconditionalBr (Name "return"%string))).

Definition inst_12 : llvm_cmd := (CMD_Phi 12 (Phi (Name "retval.0"%string) (TYPE_I 32) [((Name "if.then3"%string), (EXP_Integer (1)%Z)); ((Name "if.else4"%string), (EXP_Integer (0)%Z))])).

Definition inst_13 : llvm_cmd := (CMD_Term 13 (TERM_Ret ((TYPE_I 32), (EXP_Ident (ID_Local (Name "retval.0"%string)))))).

Definition bb_0 : llvm_block := (mk_block (Name "entry"%string) [inst_0; inst_1; inst_2; inst_3; inst_4] None).

Definition bb_1 : llvm_block := (mk_block (Name "if.then"%string) [inst_5] None).

Definition bb_2 : llvm_block := (mk_block (Name "if.else"%string) [inst_7] None).

Definition bb_3 : llvm_block := (mk_block (Name "if.end"%string) [inst_8; inst_9] None).

Definition bb_4 : llvm_block := (mk_block (Name "if.then3"%string) [inst_10] None).

Definition bb_5 : llvm_block := (mk_block (Name "if.else4"%string) [inst_11] None).

Definition bb_6 : llvm_block := (mk_block (Name "return"%string) [inst_12; inst_13] None).

Definition decl_main : llvm_declaration := (mk_declaration (Name "main"%string) (TYPE_Function (TYPE_I 32) [] false) ([], [[]; []]) [] []).

Definition decl_klee_make_symbolic_int32 : llvm_declaration := (mk_declaration (Name "klee_make_symbolic_int32"%string) (TYPE_Function (TYPE_I 32) [] false) ([], [[]; []]) [] []).

Definition decl_klee_assume_bool : llvm_declaration := (mk_declaration (Name "klee_assume_bool"%string) (TYPE_Function TYPE_Void [(TYPE_I 1)] false) ([], [[]; []]) [] []).

Definition def_main : llvm_definition := (mk_definition _ decl_main [] (mk_cfg (Name "entry"%string) [bb_0; bb_1; bb_2; bb_3; bb_4; bb_5; bb_6])).

Definition mdl : llvm_module := (mk_module None None None [] [] [decl_klee_make_symbolic_int32; decl_klee_assume_bool] [def_main]).

Lemma is_supported_inst_0 : (is_supported_cmd inst_0).
Proof.
{
  apply IS_INSTR_Call.
  intros arg Hin.
  destruct Hin.
}
Qed.

Lemma is_supported_inst_1 : (is_supported_cmd inst_1).
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

Lemma is_supported_inst_2 : (is_supported_cmd inst_2).
Proof.
{
  apply IS_INSTR_VoidCall.
  intros arg Hin.
  destruct Hin as [Hin | Hin].
  {
    inversion Hin.
    subst.
    apply IS_FunctionArg.
    {
      apply IS_EXP_Ident.
    }
  }
  destruct Hin.
}
Qed.

Lemma is_supported_inst_3 : (is_supported_cmd inst_3).
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

Lemma is_supported_inst_4 : (is_supported_cmd inst_4).
Proof.
{
  apply IS_Term_Br.
  {
    apply IS_EXP_Ident.
  }
}
Qed.

Lemma is_supported_inst_5 : (is_supported_cmd inst_5).
Proof.
{
  apply IS_Term_UnconditionalBr.
}
Qed.

Lemma is_supported_inst_7 : (is_supported_cmd inst_7).
Proof.
{
  apply IS_Term_Unreachable.
}
Qed.

Lemma is_supported_inst_8 : (is_supported_cmd inst_8).
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

Lemma is_supported_inst_9 : (is_supported_cmd inst_9).
Proof.
{
  apply IS_Term_Br.
  {
    apply IS_EXP_Ident.
  }
}
Qed.

Lemma is_supported_inst_10 : (is_supported_cmd inst_10).
Proof.
{
  apply IS_Term_UnconditionalBr.
}
Qed.

Lemma is_supported_inst_11 : (is_supported_cmd inst_11).
Proof.
{
  apply IS_Term_UnconditionalBr.
}
Qed.

Lemma is_supported_inst_12 : (is_supported_cmd inst_12).
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
      apply IS_EXP_Integer.
    }
  }
  destruct Hin.
}
Qed.

Lemma is_supported_inst_13 : (is_supported_cmd inst_13).
Proof.
{
  apply IS_Term_Ret.
  {
    apply IS_EXP_Ident.
  }
}
Qed.

Lemma is_supported_bb_0 : (is_supported_block (mk_block (Name "entry"%string) [inst_0; inst_1; inst_2; inst_3; inst_4] None)).
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
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_3.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_4.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_1 : (is_supported_block (mk_block (Name "if.then"%string) [inst_5] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
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

Lemma is_supported_bb_2 : (is_supported_block (mk_block (Name "if.else"%string) [inst_7] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_7.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_3 : (is_supported_block (mk_block (Name "if.end"%string) [inst_8; inst_9] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_8.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_9.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_4 : (is_supported_block (mk_block (Name "if.then3"%string) [inst_10] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_10.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_5 : (is_supported_block (mk_block (Name "if.else4"%string) [inst_11] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_11.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_6 : (is_supported_block (mk_block (Name "return"%string) [inst_12; inst_13] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_12.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_13.
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
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_4.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_5.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_6.
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

Definition s_0 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 0) inst_0 [inst_1; inst_2; inst_3; inst_4] None (empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_1 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 1) inst_1 [inst_2; inst_3; inst_4] None ((Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_2 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 2) inst_2 [inst_3; inst_4] None ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_3 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 3) inst_3 [inst_4] None ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition s_4 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 4) inst_4 [] None ((Name "cmp1"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition s_5 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "if.then"%string) 5) inst_5 [] (Some (Name "entry"%string)) ((Name "cmp1"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition s_6 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "if.end"%string) 8) inst_8 [inst_9] (Some (Name "if.then"%string)) ((Name "cmp1"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition s_7 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "if.end"%string) 9) inst_9 [] (Some (Name "if.then"%string)) ((Name "cmp2"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Var Sort_BV32 (fresh_name [])) (AST_Const Sort_BV32 (Int32.repr 3))))); (Name "cmp1"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition s_8 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "if.else4"%string) 11) inst_11 [] (Some (Name "if.end"%string)) ((Name "cmp2"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Var Sort_BV32 (fresh_name [])) (AST_Const Sort_BV32 (Int32.repr 3))))); (Name "cmp1"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition s_9 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "return"%string) 12) inst_12 [inst_13] (Some (Name "if.else4"%string)) ((Name "cmp2"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Var Sort_BV32 (fresh_name [])) (AST_Const Sort_BV32 (Int32.repr 3))))); (Name "cmp1"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition s_10 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "return"%string) 13) inst_13 [] (Some (Name "if.else4"%string)) ((Name "retval.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); (Name "cmp2"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Var Sort_BV32 (fresh_name [])) (AST_Const Sort_BV32 (Int32.repr 3))))); (Name "cmp1"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))))); (Name "call"%string) !-> Some ((Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name [])))); empty_smt_store) [] gs (extend_names []) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) mdl).

Definition t_10 : execution_tree := (t_leaf s_10).

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

Lemma UNSAT_1 : (unsat (AST_BinOp Sort_BV1 SMT_And (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Var Sort_BV32 (fresh_name [])) (AST_Const Sort_BV32 (Int32.repr 3))))).
Proof.
Admitted.

Lemma UNSAT_0 : (unsat (AST_BinOp Sort_BV1 SMT_And (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) (AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 (Int1.repr 0)) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name [])))))).
Proof.
Admitted.

Lemma L_10 : (safe_et_opt t_10).
Proof.
apply Safe_Leaf_Ret.
Qed.

Lemma L_9 : (safe_et_opt t_9).
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

Lemma L_8 : (safe_et_opt t_8).
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

Lemma L_7 : (safe_et_opt t_7).
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
      apply (equiv_smt_expr_unsat ((AST_BinOp Sort_BV1 SMT_And (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Var Sort_BV32 (fresh_name [])) (AST_Const Sort_BV32 (Int32.repr 3))))) (_)).
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
            apply (implied_negated_condition (_) (_) ((AST_BinOp Sort_BV1 SMT_And (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Var Sort_BV32 (fresh_name [])) (AST_Const Sort_BV32 (Int32.repr 3)))))).
            {
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
    }
  }
}
Qed.

Lemma L_6 : (safe_et_opt t_6).
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
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
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
            apply (implied_condition (_) (_) ((AST_BinOp Sort_BV1 SMT_And (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) (AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 (Int1.repr 0)) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name []))))))).
            {
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
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_BinOp Sort_BV1 SMT_And (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 7)) (AST_Var Sort_BV32 (fresh_name []))) (AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 (Int1.repr 0)) (AST_CmpOp Sort_BV32 SMT_Slt (AST_Const Sort_BV32 (Int32.repr 0)) (AST_Var Sort_BV32 (fresh_name [])))))) (_)).
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

Lemma L_3 : (safe_et_opt t_3).
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

Lemma L_2 : (safe_et_opt t_2).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_void_call.
    intros H.
    inversion H.
  }
  {
    intros s Hstep.
    inversion Hstep.
    {
      inversion H14.
    }
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
          inversion H16.
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
            apply injection_some in H16.
            apply injection_ast in H16.
            subst.
            apply equiv_smt_expr_normalize_simplify.
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
    apply not_error_call.
  }
  {
    intros s Hstep.
    inversion Hstep.
    {
      inversion H16.
    }
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

