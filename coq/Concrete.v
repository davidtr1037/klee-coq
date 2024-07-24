From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.

Record inst_counter := mk_inst_counter {
  fid : function_id;
  bid : block_id;
  cid : cmd_id;
}.

(* TODO: why option? *)
Definition dv_store := total_map (option dynamic_value).

Definition empty_dv_store := empty_map (Some DV_Undef).

Definition global_store := dv_store.

(*
Record frame := mk_frame {
  local_store : store;
  return_ic : inst_counter;
  return_var : raw_id;
}.
*)

Inductive frame : Type :=
  Frame (s : dv_store) (ic : inst_counter) (v : raw_id)
.

(* TODO: define as an inductive type? *)
Record state : Type := mk_state {
  ic : inst_counter;
  cmd : llvm_cmd;
  block : list llvm_cmd;
  store : dv_store;
  stack : list frame;
  globals : global_store;
  module : llvm_module;
}.

Definition build_inst_counter (m : llvm_module) (d : llvm_definition) : option inst_counter :=
  match (entry_block d) with
  | Some b =>
      match (get_first_cmd_id b) with
      | Some cid => Some (mk_inst_counter (dc_name (df_prototype d)) (blk_id b) cid)
      | _ => None
      end
  | _ => None
  end
.

Definition build_local_store (m : llvm_module) (d : llvm_definition) := empty_dv_store.

Definition get_global_initializer (g : llvm_global) : option dynamic_value :=
  match (g_exp g) with
  | Some e => eval_constant_exp (g_typ g) e
  | _ => Some DV_Undef (* TODO: check against the specifiction *)
  end
.

Fixpoint build_global_store_internal (s : dv_store) (l : list llvm_global) :=
  match l with
  | g :: t => build_global_store_internal ((g_ident g) !-> (get_global_initializer g); s) t
  | nil => s
  end
.

Definition build_global_store (m : llvm_module) :=
  build_global_store_internal empty_dv_store (m_globals m)
.

(* TODO: assumes that there are no parameters *)
Definition init_state (m : llvm_module) (d : llvm_definition) : option state :=
  match (build_inst_counter m d) with
  | Some ic =>
      match (entry_block d) with
      | Some b =>
          match (blk_cmds b) with
          | cmd :: tail =>
              Some (mk_state
                ic
                cmd
                tail
                (build_local_store m d)
                []
                (build_global_store m)
                m
              )
          | _ => None
          end
      | None => None
      end
  | None => None
  end
.

Definition lookup_ident (s : dv_store) (g : global_store) (id : ident) : option dynamic_value :=
  match id with
  | ID_Local x => s x
  | ID_Global x => g x
  end
.

(* TODO: why vellvm passes dtyp? *)
Fixpoint eval_exp (s : dv_store) (g : global_store) (t : option typ) (e : exp typ) : option dynamic_value :=
  match e with
  | EXP_Ident id => lookup_ident s g id
  | EXP_Integer n =>
      match t with
      | Some (TYPE_I bits) => make_dv bits n
      | _ => None
      end
  | EXP_Float f => None
  | EXP_Double f => None
  | EXP_Hex f => None
  | EXP_Bool b => Some (make_bool b)
  | EXP_Null => None
  | EXP_Zero_initializer => None
  | EXP_Cstring elts => None
  | EXP_Undef => Some DV_Undef
  | EXP_Poison => None
  | EXP_Struct fields => None
  | EXP_Packed_struct fields => None
  | EXP_Array elts => None
  | EXP_Vector elts => None
  | OP_IBinop iop t v1 v2 =>
      match (eval_exp s g (Some t) v1, eval_exp s g (Some t) v2) with
      | (Some dv1, Some dv2) => eval_ibinop iop dv1 dv2
      | (_, _) => None
      end
  | OP_ICmp icmp t v1 v2 =>
      match (eval_exp s g (Some t) v1, eval_exp s g (Some t) v2) with
      | (Some dv1, Some dv2) => eval_icmp icmp dv1 dv2
      | (_, _) => None
      end
  | OP_FBinop fop _ _ _ _ => None
  | OP_FCmp _ _ _ _ => None
  | OP_Conversion conv t1 e t2 =>
      match eval_exp s g (Some t1) e with
      | Some dv => convert conv dv t1 t2
      | _ => None
      end
  | OP_GetElementPtr _ _ _ => None
  | OP_ExtractElement _ _ => None
  | OP_InsertElement _ _ _ => None
  | OP_ShuffleVector _ _ _ => None
  | OP_ExtractValue _ _ => None
  | OP_InsertValue _ _ _ => None
  | OP_Select _ _ _ => None
  | OP_Freeze _ => None
  end
.

Definition next_inst_counter (pc : inst_counter) (c : llvm_cmd) : inst_counter :=
  mk_inst_counter (fid pc) (bid pc) (get_cmd_id c)
.

Inductive step : state -> state -> Prop :=
  | Step_OP : forall pc cid v e c b f s g m dv,
      (eval_exp f g None e) = Some dv ->
      step
        (mk_state pc (CMD_Inst cid (INSTR_Op v e)) (c :: b) f s g m)
        (mk_state (next_inst_counter pc c) c b (v !-> Some dv; f) s g m)
.
