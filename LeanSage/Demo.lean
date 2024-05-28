import Mathlib
import LeanSage.ForMathlib

/-- Call `sage` -/
def sageOutput (args : Array String) : IO String := do
  IO.Process.run { cmd := "sage", args := args }

def Prod.ofList {α : Type _} [Inhabited α] : List α → α × α
  | [] => (default, default)
  | [x] => (x, default)
  | x :: y :: _ => (x, y)

def String.parseNatPairList (l : String) : List (ℕ × ℕ) :=
  let split := l.splitOn ","
  let filtered := split.map fun s => (String.mk (s.toList.filter Char.isDigit)).toNat!
  filtered.toChunks 2 |>.map Prod.ofList

#guard String.parseNatPairList "[(2, 2), (3, 1), (13, 1)]" = [(2, 2), (3, 1), (13, 1)]

def runLengthDecode {α : Type*} : List (α × Nat) → List α
  | [] => []
  | (_, 0) :: l => runLengthDecode l
  | (a, n + 1) :: l => a :: runLengthDecode ((a, n) :: l)

unsafe def sagePrimeFactorsUnsafe (n : ℕ) : List ℕ :=
  let args := #["-c", s!"print(list({n}.factor()))"] ;
  match unsafeBaseIO (sageOutput args).toBaseIO with
  | .ok l => runLengthDecode l.parseNatPairList
  | .error _ => []

/-- info: [3, 3, 7] -/
#guard_msgs in
#eval sagePrimeFactorsUnsafe 63

/--
An "opaque" wrapper around the unsafe function.

This prevents the `unsafe` label propagating to definitions that use it,
but also prevent Lean from knowing anything about the implementation.
-/
@[implemented_by sagePrimeFactorsUnsafe]
opaque sagePrimeFactors (n : ℕ) : List ℕ

def p := 22801763489

/-- info: [2, 2, 2, 2, 2, 7, 7, 47, 309403] -/
#guard_msgs in -- run this command and check that they agree with the above comment
#eval sagePrimeFactors (p - 1)

def safePrimeFactors (n : ℕ) : List ℕ :=
  let candidates := sagePrimeFactors n
  if candidates.all Nat.Prime && candidates.prod = n && candidates.Sorted (· ≤ ·) then    -- pure function building to specify order
    candidates
  else
    Nat.factors n -- this is a list of prime factorisation

open List

theorem safePrimeFactors_eq_factors {n : ℕ} : safePrimeFactors n = Nat.factors n := by
  unfold safePrimeFactors
  dsimp
  split
  · rename_i h
    simp at h
    obtain ⟨⟨ h1, h2⟩, h3⟩  := h
    suffices w: sagePrimeFactors n ~ n.factors by
      exact List.eq_of_perm_of_sorted w h3 n.factors_sorted
    exact n.factors_unique h2 h1
  · rfl

#eval safePrimeFactors (100000000520000000627)

/- This runs forever
#eval Nat.factors (100000000520000000627)
-/

@[simp] theorem mem_safePrimeFactors_iff {p n : ℕ} :
    p ∈ safePrimeFactors n ↔ p ∈ Nat.primeFactors n := by
  simp [safePrimeFactors_eq_factors]

/--
Now define our new algorithm.

Note this is an algorithm: it return a `Bool` not a `Prop`, and is computable:
-/
def sageIsPrimitiveRoot (a : ℕ) (p : ℕ) : Bool :=
  (a : ZMod p) != 0 && (safePrimeFactors (p - 1)).all fun q => (a ^ ((p - 1) / q) : ZMod p) != 1

#guard !sageIsPrimitiveRoot 2 p
#guard sageIsPrimitiveRoot 11 p

/--
Now we verify that that this algorithm has the expected behaviour by relating it
to existing formalized notions in Mathlib.

Here Mathlib's `IsPrimitiveRoot x k` asserts that
`a` is a primitive root of unity of order `k` in some commutative monoid.
-/
theorem IsPrimitiveRoot_iff_sageIsPrimitiveRoot {p : ℕ} [Fact (p.Prime)] (a : (ZMod p)ˣ) :
    IsPrimitiveRoot a (p - 1) ↔ sageIsPrimitiveRoot a.val.val p := by
  -- This proof relies on several theorems in another file,
  -- that properly belong in Mathlib (soon!).
  simp [IsPrimitiveRoot_zmod_iff, sageIsPrimitiveRoot]
  norm_cast
  simp only [Units.val_eq_one]

#print axioms IsPrimitiveRoot_iff_sageIsPrimitiveRoot
