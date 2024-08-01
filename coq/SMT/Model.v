From Coq Require Import Strings.String.

From SE Require Import DynamicValue.
(* TODO: avoid this dependency *)
From SE Require Import LLVMAst.
From SE.SMT Require Import Expr.
From SE.Utils Require Import StringMap.

Inductive symbol : Type :=
  | Symbol_BV (s : string)
  | Symbol_Array (s : string)
.

Record smt_model := mk_smt_model {
  bv_model : total_map dynamic_value;
}.

(* TODO: define default model *)

Fixpoint smt_eval (m : smt_model) (e : smt_expr) : option dynamic_value :=
  match e with
  | SMT_Const_I1 n => Some (DV_I1 n)
  | SMT_Const_I8 n => Some (DV_I8 n)
  | SMT_Const_I16 n => Some (DV_I16 n)
  | SMT_Const_I32 n => Some (DV_I32 n)
  | SMT_Const_I64 n => Some (DV_I64 n)
  | SMT_Var_I1 x => Some ((bv_model m) x)
  | SMT_Var_I8 x => Some ((bv_model m) x)
  | SMT_Var_I16 x => Some ((bv_model m) x)
  | SMT_Var_I32 x => Some ((bv_model m) x)
  | SMT_Var_I64 x => Some ((bv_model m) x)
  | SMT_Add e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (Add false true) dv1 dv2
      | _, _ => None
      end
  | SMT_Sub e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (Sub false true) dv1 dv2
      | _, _ => None
      end
  | SMT_Mul e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (Mul false true) dv1 dv2
      | _, _ => None
      end
  | SMT_UDiv e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (UDiv false) dv1 dv2
      | _, _ => None
      end
  | SMT_SDiv e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (SDiv false) dv1 dv2
      | _, _ => None
      end
  | SMT_URem e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_ibinop URem dv1 dv2
      | _, _ => None
      end
  | SMT_SRem e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_ibinop SRem dv1 dv2
      | _, _ => None
      end
  | SMT_And e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_ibinop And dv1 dv2
      | _, _ => None
      end
  | SMT_Or e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_ibinop Or dv1 dv2
      | _, _ => None
      end
  | SMT_Xor e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_ibinop Xor dv1 dv2
      | _, _ => None
      end
  | SMT_Shl e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (Shl false true) dv1 dv2
      | _, _ => None
      end
  | SMT_LShr e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (LShr false) dv1 dv2
      | _, _ => None
      end
  | SMT_AShr e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      (* TODO: which flags should be used? *)
      | Some dv1, Some dv2 => eval_ibinop (AShr false) dv1 dv2
      | _, _ => None
      end
  | SMT_Eq e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Eq dv1 dv2
      | _, _ => None
      end
  | SMT_Ne e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Ne dv1 dv2
      | _, _ => None
      end
  | SMT_Ult e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Ult dv1 dv2
      | _, _ => None
      end
  | SMT_Ule e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Ule dv1 dv2
      | _, _ => None
      end
  | SMT_Ugt e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Ugt dv1 dv2
      | _, _ => None
      end
  | SMT_Uge e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Uge dv1 dv2
      | _, _ => None
      end
  | SMT_Slt e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Slt dv1 dv2
      | _, _ => None
      end
  | SMT_Sle e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Sle dv1 dv2
      | _, _ => None
      end
  | SMT_Sgt e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Sgt dv1 dv2
      | _, _ => None
      end
  | SMT_Sge e1 e2 =>
      match (smt_eval m e1), (smt_eval m e1) with
      | Some dv1, Some dv2 => eval_icmp Sge dv1 dv2
      | _, _ => None
      end
  | SMT_ZExt e w => None
  | SMT_SExt e w => None
  | SMT_ITE e1 e2 e3 =>
      match (smt_eval m e1) with
      | Some (DV_I1 b) =>
          if eq b one then
            smt_eval m e2
          else
            smt_eval m e3
      | _ => None
      end
  | SMT_Not e => None
  | SMT_Concat e1 e2 => None
  | SMT_Extract e i w => None
  | SMT_Select a e => None
  end
.

Definition sat_via (e : smt_expr) (m : smt_model) :=
  smt_eval m e = Some bv_true.

Definition sat (e : smt_expr) :=
  exists (m : smt_model), sat_via e m.

Definition unsat (e : smt_expr) := ~ sat e.

(* TODO: ... *)
Inductive subexpr : smt_expr -> smt_expr -> Prop :=
.

Inductive equiv_smt_expr : smt_expr -> smt_expr -> Prop :=
  | EquivSMTExpr : forall e1 e2,
      (forall m, exists dv, smt_eval m e1 = Some dv /\ smt_eval m e2 = Some dv) ->
      equiv_smt_expr e1 e2
.
