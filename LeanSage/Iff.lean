import Mathlib
import LeanSage.ForMathlib

open Nat

def sageOutput (args : Array String) : IO String := do
  IO.Process.run { cmd := "sage", args := args }

def String.parseNatList (l : String) : List ℕ :=
  (((l.drop 1).dropRight 2).split (. = ' ')).map
    (fun s => s.stripSuffix ",") |> .map String.toNat!

unsafe def sagePrimeFactorsUnsafe (n : ℕ) : List ℕ :=
  let args := #["-c", s!"print(prime_factors({n}))"] ;
  match unsafeBaseIO (sageOutput args).toBaseIO with
  | .ok l => l.parseNatList
  | .error _ => []

@[implemented_by sagePrimeFactorsUnsafe]
opaque sagePrimeFactors (n : ℕ) : List ℕ

@[simp] axiom mem_sagePrimeFactors_iff {p n : ℕ} : p ∈ sagePrimeFactors n ↔ p ∈ primeFactors n

def sageIsPrimitiveRoot (a : ℕ) (p : ℕ) : Bool :=
  (a : ZMod p) != 0 && (sagePrimeFactors (p - 1)).all fun q => (a ^ ((p - 1) / q) : ZMod p) != 1

theorem IsPrimitiveRoot_iff_sageIsPrimitiveRoot {p : ℕ} [Fact (p.Prime)] (a : ZMod p) :
    IsPrimitiveRoot a (p - 1) ↔ sageIsPrimitiveRoot a.val p := by
  simp [IsPrimitiveRoot_iff, sageIsPrimitiveRoot]
