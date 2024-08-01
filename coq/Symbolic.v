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

(* TODO: smt_store -> sym_store? *)

Definition smt_store := total_map smt_expr.

Definition global_smt_store := smt_store.

Inductive sym_frame : Type :=
  | Sym_Frame (s : smt_store) (ic : inst_counter) (pbid : option block_id) (v : raw_id)
  | Sym_Frame_NoReturn (s : smt_store) (ic : inst_counter) (pbid : option block_id)
.

(* TODO: define as an inductive type? *)
Record sym_state : Type := mk_state {
  sym_ic : inst_counter;
  sym_cmd : llvm_cmd;
  sym_block : list llvm_cmd;
  sym_prev_bid : option block_id; (* TODO: add to inst_counter? *)
  sym_store : smt_store; (* TODO: rename *)
  sym_stack : list sym_frame;
  sym_globals : global_smt_store;
  sym_symbolics : list string;
  sym_pc : smt_expr;
  sym_module : llvm_module;
}.
