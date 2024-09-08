From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE.Numeric Require Import Integers.

From SE.Utils Require Import StringMap.

Variant smt_binop : Type :=
  | SMT_Add
  | SMT_Sub
  | SMT_Mul
  | SMT_UDiv
  | SMT_SDiv
  | SMT_URem
  | SMT_SRem
  | SMT_And
  | SMT_Or
  | SMT_Xor
  | SMT_Shl
  | SMT_LShr
  | SMT_AShr
.

Variant smt_cmpop : Type :=
  | SMT_Eq
  | SMT_Ne
  | SMT_Ult
  | SMT_Ule
  | SMT_Ugt
  | SMT_Uge
  | SMT_Slt
  | SMT_Sle
  | SMT_Sgt
  | SMT_Sge
.

Inductive smt_sort : Type :=
  | Sort_BV1
  | Sort_BV8
  | Sort_BV16
  | Sort_BV32
  | Sort_BV64
.

Definition smt_sort_to_int_type (s : smt_sort) :=
  match s with
  | Sort_BV1 => int1
  | Sort_BV8 => int8
  | Sort_BV16 => int16
  | Sort_BV32 => int32
  | Sort_BV64 => int64
  end
.

Inductive typed_smt_ast : smt_sort -> Type :=
  | TypedSMT_Const :
      forall (s : smt_sort) (t : (smt_sort_to_int_type s)), typed_smt_ast s
  | TypedSMT_Var :
      forall (s : smt_sort) (x : string), typed_smt_ast s
  | TypedSMT_BinOp :
      forall (s : smt_sort) (op : smt_binop) (e1 e2 : typed_smt_ast s), typed_smt_ast s
  | TypedSMT_CmpOp :
      forall (s : smt_sort) (op : smt_cmpop) (e1 e2 : typed_smt_ast s), typed_smt_ast s
  | TypedSMT_Not :
      forall (s : smt_sort) (e : typed_smt_ast s), typed_smt_ast s
.

(* TODO: use sigT? *)
Inductive typed_smt_expr : Type :=
  | TypedSMTExpr (s : smt_sort) (ast : typed_smt_ast s)
.

Definition smt_true := (TypedSMTExpr Sort_BV1 (TypedSMT_Const Sort_BV1 one)).
Definition smt_false := (TypedSMTExpr Sort_BV1 (TypedSMT_Const Sort_BV1 zero)).
