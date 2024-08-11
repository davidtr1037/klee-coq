From Coq Require Import List.

Import ListNotations.

From SE Require Import CFG.
From SE Require Import LLVMAst.

Inductive is_supported_cmd : llvm_cmd -> Prop :=
  | IS_Phi : forall n p,
      is_supported_cmd (CMD_Phi n p)
  | IS_EXP_Ident : forall n v id,
      is_supported_cmd (CMD_Inst n (INSTR_Op v (EXP_Ident id)))
  | IS_EXP_Integer : forall n v x,
      is_supported_cmd (CMD_Inst n (INSTR_Op v (EXP_Integer x)))
  | IS_OP_IBinop : forall n v t e1 e2,
      is_supported_cmd (CMD_Inst n (INSTR_Op v (OP_IBinop (Add false false) t e1 e2)))
  | IS_Term : forall n t,
      is_supported_cmd (CMD_Term n t)
.

Inductive is_supported_block : llvm_block -> Prop :=
  | IS_Block : forall b,
      (forall c, In c (blk_cmds b) -> is_supported_cmd c) ->
      is_supported_block b
.

Inductive is_supported_definition : llvm_definition -> Prop :=
  | IS_Definition : forall d,
      (forall b, In b (blks (df_body d)) -> is_supported_block b) ->
      is_supported_definition d
.

Inductive is_supported_module : llvm_module -> Prop :=
  | IS_Module : forall mdl,
      (forall d, In d (m_definitions mdl) -> is_supported_definition d) ->
      is_supported_module mdl
.
