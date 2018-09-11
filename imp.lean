inductive aexp : Type
| ANum   : nat  -> aexp   
| APlus  : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult  : aexp -> aexp -> aexp

inductive bexp : Type
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

open aexp bexp

def aeval : aexp -> nat
|(ANum n)      :=  n
|(APlus a1 a2) := (aeval a1) + (aeval a2)
|(AMinus a1 a2):= (aeval a1) - (aeval a2)
|(AMult a1 a2) := (aeval a1) * (aeval a2)

example : aeval (APlus (ANum 2) (ANum 2)) = 4 := rfl

def beval : bexp -> bool
| BTrue       := true
| BFalse      := false
|(BEq  a1 a2) := (aeval a1) = (aeval a2)
|(BLe  a1 a2) := (aeval a1) <= (aeval a2)
|(BNot b1)    := bnot $ beval b1
|(BAnd b1 b2) := (beval b1) && (beval b2)

example : beval (BEq (APlus (ANum 2) (ANum 3)) (ANum 5)) = true := rfl


