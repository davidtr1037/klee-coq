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
From SE Require Import Symbolic.
From SE Require Import ProofGeneration.
From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.
Definition inst_0 : llvm_cmd :=
  (CMD_Inst
    0
    (INSTR_Call
      (Name
        "call"%string
      )
      (
        (TYPE_I
          32
        ),
        (EXP_Ident
          (ID_Global
            (Name
              "klee_make_symbolic_int32"%string
            )
          )
        )
      )
      []
      []
    )
  ).

Definition inst_1 : llvm_cmd :=
  (CMD_Inst
    1
    (INSTR_Op
      (Name
        "cmp"%string
      )
      (OP_ICmp
        Sgt
        (TYPE_I
          32
        )
        (EXP_Ident
          (ID_Local
            (Name
              "call"%string
            )
          )
        )
        (EXP_Integer
          (7)%Z
        )
      )
    )
  ).

Definition inst_2 : llvm_cmd :=
  (CMD_Inst
    2
    (INSTR_VoidCall
      (
        TYPE_Void,
        (EXP_Ident
          (ID_Global
            (Name
              "klee_assume_bool"%string
            )
          )
        )
      )
      [
        (
          (
            (TYPE_I
              1
            ),
            (EXP_Ident
              (ID_Local
                (Name
                  "cmp"%string
                )
              )
            )
          ),
          []
        )
      ]
      []
    )
  ).

Definition inst_3 : llvm_cmd :=
  (CMD_Inst
    3
    (INSTR_Op
      (Name
        "cmp1"%string
      )
      (OP_ICmp
        Sgt
        (TYPE_I
          32
        )
        (EXP_Ident
          (ID_Local
            (Name
              "call"%string
            )
          )
        )
        (EXP_Integer
          (3)%Z
        )
      )
    )
  ).

Definition inst_4 : llvm_cmd :=
  (CMD_Term
    4
    (TERM_Br
      (
        (TYPE_I
          1
        ),
        (EXP_Ident
          (ID_Local
            (Name
              "cmp1"%string
            )
          )
        )
      )
      (Name
        "if.then"%string
      )
      (Name
        "if.else"%string
      )
    )
  ).

Definition inst_5 : llvm_cmd :=
  (CMD_Term
    5
    (TERM_UnconditionalBr
      (Name
        "if.end"%string
      )
    )
  ).

Definition inst_6 : llvm_cmd :=
  (CMD_Term
    6
    TERM_Unreachable
  ).

Definition inst_7 : llvm_cmd :=
  (CMD_Term
    7
    (TERM_Ret
      (
        (TYPE_I
          32
        ),
        (EXP_Integer
          (0)%Z
        )
      )
    )
  ).

Definition bb_0 : llvm_block :=
  (mk_block
    (Name
      "entry"%string
    )
    [
      inst_0;
      inst_1;
      inst_2;
      inst_3;
      inst_4
    ]
    None
  ).

Definition bb_1 : llvm_block :=
  (mk_block
    (Name
      "if.then"%string
    )
    [
      inst_5
    ]
    None
  ).

Definition bb_2 : llvm_block :=
  (mk_block
    (Name
      "if.else"%string
    )
    [
      inst_6
    ]
    None
  ).

Definition bb_3 : llvm_block :=
  (mk_block
    (Name
      "if.end"%string
    )
    [
      inst_7
    ]
    None
  ).

Definition def_0 : llvm_definition :=
  (mk_definition
    _
    (mk_declaration
      (Name
        "main"%string
      )
      (TYPE_Function
        (TYPE_I
          32
        )
        []
        false
      )
      (
        [],
        [
          [];
          []
        ]
      )
      []
      []
    )
    []
    (mk_cfg
      (Name
        "entry"%string
      )
      [
        bb_0;
        bb_1;
        bb_2;
        bb_3
      ]
    )
  ).

Definition mdl : llvm_module :=
  (mk_module
    None
    None
    None
    []
    []
    []
    [
      def_0
    ]
  ).


