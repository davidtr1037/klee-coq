From Coq Require Import ZArith.

From SE.Numeric Require Import Integers.

Module Wordsize_1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof.
    unfold wordsize; congruence.
  Qed.
End Wordsize_1.

Module Int1 := Make(Wordsize_1).
Module Int8 := Byte.
Module Int32 := Int.

Definition int1 := Int1.int.
Definition int8 := Int8.int.
Definition int16 := Int16.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Inductive dynamic_int : Type :=
  | DI_I1 (n : int1)
  | DI_I8 (n : int8)
  | DI_I16 (n : int16)
  | DI_I32 (n : int32)
  | DI_I64 (n : int64)
.

Definition di_true := DI_I1 (Int1.repr 1%Z).
Definition di_false := DI_I1 (Int1.repr 0%Z).
