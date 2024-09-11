From Coq Require Import Logic.Eqdep.
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
  | TypedAST_Const :
      forall (s : smt_sort) (n : (smt_sort_to_int_type s)), typed_smt_ast s
  | TypedAST_Var :
      forall (s : smt_sort) (x : string), typed_smt_ast s
  | TypedAST_BinOp :
      forall (s : smt_sort) (op : smt_binop) (e1 e2 : typed_smt_ast s), typed_smt_ast s
  | TypedAST_CmpOp :
      forall (s : smt_sort) (op : smt_cmpop) (e1 e2 : typed_smt_ast s), typed_smt_ast Sort_BV1
  | TypedAST_Not :
      forall (s : smt_sort) (e : typed_smt_ast s), typed_smt_ast s
.

Definition smt_ast_bool := typed_smt_ast Sort_BV1.
Definition smt_ast_true := TypedAST_Const Sort_BV1 one.
Definition smt_ast_false := TypedAST_Const Sort_BV1 zero.

(* TODO: use sigT? *)
Inductive typed_smt_expr : Type :=
  | TypedSMTExpr (s : smt_sort) (ast : typed_smt_ast s)
.

Definition get_sort (e : typed_smt_expr) : smt_sort :=
  match e with
  | TypedSMTExpr sort _ => sort
  end
.

Definition get_ast (e : typed_smt_expr) : (typed_smt_ast (get_sort e)) :=
  match e with
  | TypedSMTExpr _ ast => ast
  end
.

Definition smt_expr_true := (TypedSMTExpr Sort_BV1 smt_ast_true).
Definition smt_expr_false := (TypedSMTExpr Sort_BV1 smt_ast_false).

Definition make_smt_const (bits : positive) (n : Z) : option typed_smt_expr :=
  match bits with
  | 1%positive => Some (TypedSMTExpr Sort_BV1 (TypedAST_Const Sort_BV1 (Int1.repr n)))
  | 8%positive => Some (TypedSMTExpr Sort_BV8 (TypedAST_Const Sort_BV8 (Int8.repr n)))
  | 16%positive => Some (TypedSMTExpr Sort_BV16 (TypedAST_Const Sort_BV16 (Int16.repr n)))
  | 32%positive => Some (TypedSMTExpr Sort_BV32 (TypedAST_Const Sort_BV32 (Int32.repr n)))
  | 64%positive => Some (TypedSMTExpr Sort_BV64 (TypedAST_Const Sort_BV64 (Int64.repr n)))
  | _ => None
  end
.

Definition make_smt_bool (b : bool) : typed_smt_expr :=
  match b with
  | true => smt_expr_true
  | false => smt_expr_false
  end
.

Inductive subexpr : typed_smt_expr -> typed_smt_expr -> Prop :=
  | SubExpr_Refl : forall e, subexpr e e
  | SubExpr_BinOp_L : forall e op sort (ast1 ast2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort ast1) ->
      subexpr e (TypedSMTExpr sort (TypedAST_BinOp sort op ast1 ast2))
  | SubExpr_BinOp_R : forall e op sort (ast1 ast2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort ast2) ->
      subexpr e (TypedSMTExpr sort (TypedAST_BinOp sort op ast1 ast2))
  | SubExpr_CmpOp_L : forall e op sort (ast1 ast2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort ast1) ->
      subexpr e (TypedSMTExpr Sort_BV1 (TypedAST_CmpOp sort op ast1 ast2))
  | SubExpr_CmpOp_R : forall e op sort (ast1 ast2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort ast2) ->
      subexpr e (TypedSMTExpr Sort_BV1 (TypedAST_CmpOp sort op ast1 ast2))
  | SubExpr_Not : forall e sort (a : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort a) ->
      subexpr e (TypedSMTExpr sort (TypedAST_Not sort a))
.

Inductive contains_var : typed_smt_expr -> string -> Prop :=
  | ContainsVar : forall sort x e,
      subexpr (TypedSMTExpr sort (TypedAST_Var sort x)) e -> contains_var e x
.

Lemma contains_var_binop : forall x sort op (ast1 ast2 : typed_smt_ast sort),
  contains_var (TypedSMTExpr sort (TypedAST_BinOp sort op ast1 ast2)) x ->
  contains_var (TypedSMTExpr sort ast1) x \/ contains_var (TypedSMTExpr sort ast2) x.
Proof.
  intros x sort op ast1 ast2 Hc.
  inversion Hc; subst.
  inversion H; subst.
  {
    apply inj_pair2 in H5; subst.
    left.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
  {
    apply inj_pair2 in H6; subst.
    right.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
Qed.

Lemma contains_var_cmpop : forall x sort op (ast1 ast2 : typed_smt_ast sort),
  contains_var (TypedSMTExpr Sort_BV1 (TypedAST_CmpOp sort op ast1 ast2)) x ->
  contains_var (TypedSMTExpr sort ast1) x \/ contains_var (TypedSMTExpr sort ast2) x.
Proof.
  intros x sort op ast1 ast2 Hc.
  inversion Hc; subst.
  inversion H; subst.
  {
    apply inj_pair2 in H4; subst.
    left.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
  {
    apply inj_pair2 in H5; subst.
    right.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
Qed.

Lemma contains_var_not : forall x sort (ast : typed_smt_ast sort),
  contains_var (TypedSMTExpr sort (TypedAST_Not sort ast)) x ->
  contains_var (TypedSMTExpr sort ast) x.
Proof.
  intros x sort ast Hc.
  inversion Hc; subst.
  inversion H; subst.
  apply inj_pair2 in H4; subst.
  apply ContainsVar with (sort := sort0).
  assumption.
Qed.

(* TODO: remove *)
Definition create_zero_by_sort (s : smt_sort) : typed_smt_ast s :=
  match s with
  | Sort_BV1 => TypedAST_Const Sort_BV1 zero
  | Sort_BV8 => TypedAST_Const Sort_BV8 zero
  | Sort_BV16 => TypedAST_Const Sort_BV16 zero
  | Sort_BV32 => TypedAST_Const Sort_BV32 zero
  | Sort_BV64 => TypedAST_Const Sort_BV64 zero
  end
.

Fixpoint normalize (s : smt_sort) (ast : typed_smt_ast s) : typed_smt_ast s :=
  match ast with
  | TypedAST_Const sort n => TypedAST_Const sort n
  | TypedAST_Var sort x => TypedAST_Var sort x
  | TypedAST_BinOp sort op ast1 ast2 =>
      TypedAST_BinOp sort op (normalize sort ast1) (normalize sort ast2)
  | TypedAST_CmpOp sort op ast1 ast2 =>
      match op with
      | SMT_Sge => TypedAST_CmpOp sort SMT_Sgt (normalize sort ast2) (normalize sort ast1)
      | SMT_Sgt => TypedAST_CmpOp sort SMT_Sge (normalize sort ast2) (normalize sort ast1)
      | SMT_Uge => TypedAST_CmpOp sort SMT_Ugt (normalize sort ast2) (normalize sort ast1)
      | SMT_Ugt => TypedAST_CmpOp sort SMT_Uge (normalize sort ast2) (normalize sort ast1)
      | _ => TypedAST_CmpOp sort op (normalize sort ast1) (normalize sort ast2)
      end
  | TypedAST_Not sort ast =>
      let f :=
      match sort return (typed_smt_ast sort) -> (typed_smt_ast sort) with
      | Sort_BV1 =>
          TypedAST_CmpOp Sort_BV1 SMT_Eq smt_ast_false
      | Sort_BV8 => TypedAST_Not Sort_BV8
      | Sort_BV16 => TypedAST_Not Sort_BV16
      | Sort_BV32 => TypedAST_Not Sort_BV32
      | Sort_BV64 => TypedAST_Not Sort_BV64
      end in
      f (normalize sort ast)
  end
.

(*
Fixpoint simplify_ast (s : smt_sort) (ast : typed_smt_ast s) : typed_smt_ast s :=
  match ast with
  | TypedAST_BinOp sort op ast1 ast2 =>
    match op with
    | SMT_Add => ast
      match (simplify_ast sort ast1), (simplify_ast sort ast2) return (typed_smt_ast s) with
      | TypedAST_Const Sort_BV1 n1, TypedAST_Const Sort_BV1 n2 =>
          TypedAST_Const Sort_BV1 (add n1 n2)
      | TypedAST_Const Sort_BV8 n1, TypedAST_Const Sort_BV8 n2 =>
          TypedAST_Const Sort_BV8 (add n1 n2)
      | TypedAST_Const Sort_BV16 n1, TypedAST_Const Sort_BV16 n2 =>
          TypedAST_Const Sort_BV16 (add n1 n2)
      | TypedAST_Const Sort_BV32 n1, TypedAST_Const Sort_BV32 n2 =>
          TypedAST_Const Sort_BV32 (add n1 n2)
      | TypedAST_Const Sort_BV64 n1, TypedAST_Const Sort_BV64 n2 =>
          TypedAST_Const Sort_BV64 (add n1 n2)
      | _, _ => ast
      end
    | _ => ast
    end
  | _ => ast
  end
.
*)
