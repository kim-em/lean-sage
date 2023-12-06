import Mathlib

@[simps]
def zpowMulHom {G} [Group G] (g : G) : (Multiplicative ℤ) →* G where
  toFun i := g^(Multiplicative.toAdd i)
  map_one' := by simp
  map_mul' := by simp [zpow_add]

namespace AddSubgroup

def ofMultiplicative {G} [AddGroup G] (Z : Subgroup (Multiplicative G)) :
    AddSubgroup G := sorry

@[simp] theorem mem_ofMultiplicative {G} [AddGroup G]
    (Z : Subgroup (Multiplicative G)) (x : G) :
    x ∈ ofMultiplicative Z ↔ (Multiplicative.ofAdd x) ∈ Z :=
  sorry

def exponents {G} [Group G] (g : G) : AddSubgroup ℤ :=
  .ofMultiplicative (zpowMulHom g).ker

theorem mem_exponents_iff {G} [Group G] (g : G) (i : ℤ) :
    i ∈ exponents g ↔ g ^ i = 1 := by
  simp [exponents, MonoidHom.mem_ker]

theorem AddSubgroup.eq_zmultiples_int (G : AddSubgroup ℤ) (k : ℕ) (w : k ≠ 0) :
    G = zmultiples (k : ℤ) ↔
      ((k : ℤ) ∈ G ∧ ∀ q ∈ Nat.primeFactors k, (k / q : Int) ∉ G) :=
  sorry -- the interesting part

end AddSubgroup

open AddSubgroup

theorem IsPrimitiveRoot_iff {R : Type*} [CommRing R] (a : Rˣ) :
    IsPrimitiveRoot a k ↔ exponents a = zmultiples (k : Int) :=
  sorry -- just restating the definition?

theorem IsPrimitiveRoot_zmod_p_iff {p : ℕ} [Fact (p.Prime)] (a : (ZMod p)ˣ) :
    IsPrimitiveRoot a (p - 1) ↔ ∀ q ∈ Nat.primeFactors (p - 1), a ^ ((p - 1) / q) ≠ 1 := by
  simp only [IsPrimitiveRoot_iff]
  have h : p - 1 ≠ 0 := sorry
  simp only [AddSubgroup.eq_zmultiples_int _ _ h]
  simp only [mem_exponents_iff]
  simp
  -- easy from here, with Fermat's little theorem:
  sorry


-----

open Nat


@[simp] theorem ZMod.val_coe (a : ZMod p) : (a.val : ZMod p) = a := sorry


-- This theorem just belongs in Mathlib, and is surely out there!
theorem IsPrimitiveRoot_iff' {p : ℕ} [Fact (p.Prime)] (a : ZMod p) :
    IsPrimitiveRoot a (p - 1) ↔ a ≠ 0 ∧ ∀ q ∈ primeFactors (p - 1), a ^ ((p - 1) / q) ≠ 1 := by
  have p_prime : p.Prime := Fact.out
  constructor
  · rintro ⟨h1, h2⟩
    simp
    constructor
    · sorry -- easy
    intro q q_prime dvd
    specialize h2 ((p-1)/q)
    intro w
    intro h
    specialize h2 h
    have c0 : 0 < (p - 1) / q := by
      apply Nat.div_pos
      · exact le_of_dvd (Nat.sub_pos_iff_lt.mpr (Prime.one_lt p_prime)) dvd
      · exact Prime.pos q_prime
    have c1 := le_of_dvd c0 h2
    have c2 : (p - 1) / q < p - 1 :=
      div_lt_self (Nat.sub_pos_iff_lt.mpr (Prime.one_lt p_prime)) (Prime.one_lt q_prime)
    simpa using lt_of_le_of_lt c1 c2
  · -- We lift `a` in to `(ZMod p)ˣ`.
    rintro ⟨nz, h⟩
    have h0 : a * a ^ (p - 2) = 1 := by
      rw [mul_comm, ← _root_.pow_succ']
      sorry
    let au : (ZMod p)ˣ := Units.mkOfMulEqOne a (a^(p-2)) h0
    revert h
    rw [show (a : ZMod p) = (au : ZMod p) from rfl]
    clear_value au
    clear nz h0 a
    rename' au => a
    intro h
    simp
    have fermat : a^(p-1) = 1 := by
      have : Fact (p.Prime) := ⟨p_prime⟩
      have := ZMod.pow_card_sub_one_eq_one (p := p) (a := a) (by simp)
      norm_cast at this
      sorry -- slightly annoying
    constructor
    · exact fermat
    · intro l w
      by_contra ndvd
      let l' := Nat.gcd l (p - 1)
      have h1 : a ^ l' = 1 := by
        suffices a ^ (l' : ℤ) = 1 by simp_all
        rw [gcd_eq_gcd_ab l (p - 1), zpow_add, zpow_mul, zpow_coe_nat, w,
          one_zpow, zpow_mul, zpow_coe_nat, fermat, one_zpow, one_mul]
      have h2 : l' ∣ p - 1 := Nat.gcd_dvd_right l (p - 1)
      have h2b : (p - 1) / l' ≠ 1 := by
        intro r
        have : l' = p - 1 := by sorry -- easy divisibility stuff
        have dvd : p - 1 ∣ l := sorry -- "
        contradiction
      let q := minFac ((p - 1) / l')
      have q_prime : q.Prime := minFac_prime h2b
      have q_dvd : q ∣ (p - 1) / l' := minFac_dvd _
      have h4 : ∃ c, l' * c = (p - 1) / q := by
        obtain ⟨c, w⟩ := exists_eq_mul_right_of_dvd q_dvd
        use c
        sorry -- yuck!
      obtain ⟨c, h5⟩ := h4
      have h6 : a^(l' * c) = 1 := by
        rw [pow_mul, h1, one_pow]
      simp at h
      have : Fact (p.Prime) := ⟨p_prime⟩
      have h7 : a^((p-1)/q) ≠ 1 := by
        have := h q q_prime sorry p_prime.one_lt -- a divisibility argument
        -- Gross, but:
        norm_cast at this
        intro y
        rw [y] at this
        simp at this
      rw [h5] at h6
      exact h7 h6
