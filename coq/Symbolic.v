From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Relation.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

(* TODO: smt_store -> sym_store? *)

Definition smt_store := total_map smt_expr.

Definition empty_smt_store := empty_map (SMT_Const_I1 zero).

Definition global_smt_store := smt_store.

Inductive sym_frame : Type :=
  | Sym_Frame (s : smt_store) (ic : inst_counter) (pbid : option block_id) (v : raw_id)
  | Sym_Frame_NoReturn (s : smt_store) (ic : inst_counter) (pbid : option block_id)
.

(* TODO: define as an inductive type? *)
Record sym_state : Type := mk_sym_state {
  sym_ic : inst_counter;
  sym_cmd : llvm_cmd;
  sym_block : list llvm_cmd;
  sym_prev_bid : option block_id;
  sym_store : smt_store;
  sym_stack : list sym_frame;
  sym_globals : global_smt_store;
  sym_symbolics : list string;
  sym_pc : smt_expr;
  sym_module : llvm_module;
}.

(* TODO: define error_sym_state *)

(* TODO: ... *)
Definition build_local_smt_store (m : llvm_module) (d : llvm_definition) : smt_store :=
  empty_smt_store
.

Definition build_global_smt_store (m : llvm_module) : option global_smt_store := None.

Definition init_sym_state (m : llvm_module) (d : llvm_definition) : option sym_state :=
  match (build_global_smt_store m) with
  | Some gs =>
    match (build_inst_counter m d) with
    | Some ic =>
        match (entry_block d) with
        | Some b =>
            match (blk_cmds b) with
            | cmd :: tail =>
                Some (mk_sym_state
                  ic
                  cmd
                  tail
                  None
                  (build_local_smt_store m d)
                  []
                  gs
                  []
                  SMT_True
                  m
                )
            | _ => None
            end
        | None => None
        end
    | None => None
    end
  | _ => None
  end
.

Inductive sat_sym_state : smt_model -> sym_state -> Prop :=
  | Sat_State: forall sm ic c cs pbid ls stk gs syms pc m,
      sat_via pc sm ->
      sat_sym_state sm (mk_sym_state ic c cs pbid ls stk gs syms pc m)
.

Inductive unsat_sym_state : sym_state -> Prop :=
  | Unsat_State: forall ic c cs pbid ls stk gs syms pc m,
      unsat pc ->
      unsat_sym_state (mk_sym_state ic c cs pbid ls stk gs syms pc m)
.
