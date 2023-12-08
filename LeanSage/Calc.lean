import Mathlib

def p := 104729

#eval (2 : ZMod p)^2
#eval (2 : ZMod p)^10000
-- #eval (2 : ZMod p)^(p-1)

#check Fin.instMulFin
#synth Mul (Fin 3)
#check Fin.instCommRing
#synth CommRing (Fin 3)

#check Nat.mul

example : k / 2 < k + 1 :=
  calc
    k / 2 ≤ (k + 1) / 2 := Nat.div_le_div_right (Nat.le_add_right k 1)
    _ < k + 1 := Nat.div_lt_self' k 0
example : (k + 1) / 2 < k + 1 := Nat.div_lt_self' k 0

example (k n : Nat) (_ : 0 < k) (_ : k ≠ 0) : n / k * k + n % k = n := by exact
  Nat.div_add_mod' n k
