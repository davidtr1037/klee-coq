(* TODO: rename modul --> module *)
(* begin hide *)
Require Import Equalities.

From Coq Require Import ZArith List String.

From SE Require Import
     Utilities
     LLVMAst
     AstLib.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.

Import ListNotations.
Import EqvNotation.
Import MonadNotation.
Open Scope list.
Open Scope monad_scope.
(* end hide *)

Section CFG.
  Variable (T:Set).

  Inductive cmd : Set :=
  | Inst (i:instr T)
  | Term (t:terminator T)
  .

  Record cfg := mkCFG {
    init : block_id;
    blks : list (block T);
    args : list raw_id;
  }.

  Record module {Body : Set} : Set := mk_module {
    m_name : option string;
    m_target : option string;
    m_datalayout : option string;
    m_type_defs : list (ident * T);
    m_globals : list (global T);
    m_declarations : list (declaration T);
    m_definitions : list (@definition T Body);
  }.

  Definition llvm_definition := @definition T cfg.
  Definition llvm_module : Set := @module cfg.

  Definition match_function (fid : function_id) (d : llvm_definition) : option (llvm_definition) :=
    if (dc_name (df_prototype d)) =? fid then Some d else None
  .

  Definition find_function (m : llvm_module) (fid:function_id) : option (llvm_definition) :=
    find_map (match_function fid) (m_definitions m)
  .

  Definition match_block (bid : block_id) (b : block T) : bool :=
    if (blk_id b) =? bid then true else false
  .

  Definition find_block (bs: list (block T)) (bid : block_id) : option (block T) :=
    find (fun b => match_block bid b) bs
  .

End CFG.

Arguments module {_} _.
Arguments mk_module {_ _}.
Arguments m_name {_ _}.
Arguments m_target {_ _}.
Arguments m_datalayout {_ _}.
Arguments m_type_defs {_ _}.
Arguments m_globals {_ _}.
Arguments m_declarations {_ _}.
Arguments m_definitions {_ _}.
Arguments mkCFG {_}.
Arguments find_block {_}.
Arguments blks {_}.
Arguments init {_}.
Arguments args {_}.
