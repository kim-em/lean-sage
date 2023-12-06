import Mathlib

open Nat

def sagePrimeFactors (n : ℕ) : List ℕ := sorry
@[simp] axiom mem_sagePrimeFactors_iff {p n : ℕ} : p ∈ sagePrimeFactors n ↔ p.Prime ∧ p ∣ n

def isPrimitiveRoot (a : ℕ) (p : ℕ) : Bool :=
  (sagePrimeFactors (p - 1)).all fun q => a ^ ((p - 1) / q) % p ≠ 1

theorem isPrimitiveRoot_iff (a : ℕ) (p : ℕ) (prime : p.Prime) :
    isPrimitiveRoot a p ↔ IsPrimitiveRoot (a : ZMod p) (p - 1) := by
  constructor
  · intro h
    dsimp [isPrimitiveRoot] at h
    simp at h
    constructor
    · have : Fact (p.Prime) := ⟨prime⟩
      apply ZMod.pow_card_sub_one_eq_one
      sorry
    · intro l w
      by_contra
      let l' := Nat.gcd l (p - 1)
      have hp : p - 1 ≠ 0 := by simp [prime.one_lt]
      have l'nz : l' ≠ 0 := Nat.gcd_ne_zero_right hp
      have h1 : (a : ZMod p)^l' = 1 := sorry -- by Euclidean algorithm
      have h2 : l' ∣ p - 1 := Nat.gcd_dvd_right l (p - 1)
      have hp1l : ¬ ((p - 1) / l' = 0 ∨ (p - 1) / l' = 1)
      . sorry
        -- simp [div_ne_zero hp (show l' ≠ _ from l'nz)] -- ??????
      let q := (factors ((p - 1) / l')).head (by simp [hp1l])
      have q_prime : q.Prime := prime_of_mem_factors (List.head_mem _)
      have q_dvd : q ∣ (p - 1) / l' := dvd_of_mem_factors (List.head_mem _)
      -- have h4 : ∃ c, l' * c = (p - 1) / q := by sorry
      obtain ⟨c, h5⟩ := q_dvd
      have h6 : a^(l' * c) = 1 := sorry
      have h7 : a^((p-1)/q) ≠ 1 := sorry
      sorry
  · rintro ⟨h1, h2⟩
    dsimp [isPrimitiveRoot]
    simp
    intro q q_prime dvd
    specialize h2 ((p-1)/q)
    intro w
    specialize h2 ?_
    · norm_cast
      convert (ZMod.eq_iff_modEq_nat p (b := 1)).mpr _
      . simp
      . show _ % _ = _ % _
        simp [w, prime.one_lt, Nat.mod_eq_of_lt]
    have c0 : 0 < (p - 1) / q := by
      apply Nat.div_pos
      · exact le_of_dvd (Nat.sub_pos_iff_lt.mpr (Prime.one_lt prime)) dvd
      · exact Prime.pos q_prime
    have c1 := le_of_dvd c0 h2
    have c2 : (p - 1) / q < p - 1 := div_lt_self (Nat.sub_pos_iff_lt.mpr (Prime.one_lt prime)) (Prime.one_lt q_prime)
    have := lt_of_le_of_lt c1 c2
    simp at this
