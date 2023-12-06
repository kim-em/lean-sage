import Mathlib

-- From Jireh:
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/checking.20a.20subgroup.20of.20Int.20is.20generated.20by.20an.20element/near/406391580

@[simp]
lemma AddSubgroup.toIntSubmodule_zmultiples (k : ℕ) :
    (AddSubgroup.toIntSubmodule (.zmultiples (k : ℤ))) = Ideal.span {(k : ℤ)} := by
  ext n
  show n ∈ AddSubgroup.zmultiples (k : ℤ) ↔ _
  rw [Ideal.mem_span_singleton, Int.mem_zmultiples_iff]

lemma Nat.one_lt_of_mem_properDivisors {m n : ℕ} (h : m ∈ n.properDivisors) : 1 < n :=
  match n with
  | 0 => by simp at h
  | 1 => by simp at h
  | n + 2 => n.one_lt_succ_succ

lemma Nat.one_lt_div_of_mem_properDivisors {m n : ℕ} (h : m ∈ n.properDivisors) :
    1 < n / m := by
  have hm := Nat.pos_of_mem_properDivisors h
  apply lt_of_mul_lt_mul_right ?_ hm.le
  obtain ⟨h_dvd, h_lt⟩ := mem_properDivisors.mp h
  simpa [Nat.div_mul_cancel h_dvd] using h_lt

lemma Nat.mem_properDivisors_iff_exists {m n : ℕ} (hn : n ≠ 0) :
    m ∈ n.properDivisors ↔ ∃ k > 1, n = m * k := by
  constructor
  · exact fun h ↦
      ⟨n / m, one_lt_div_of_mem_properDivisors h, by
        rw [mul_comm]; exact (Nat.div_mul_cancel (mem_properDivisors.mp h).1).symm⟩
  · rintro ⟨k, hk, h⟩
    refine mem_properDivisors.mpr ⟨⟨k, h⟩, ?_⟩
    calc
      m = m * 1 := (mul_one m).symm
      _ < m * k := by
        gcongr
        exact Nat.pos_of_ne_zero fun hm ↦ hn <| by simpa [hm] using h
      _ = n     := h.symm

lemma Nat.nonempty_primeFactors {n : ℕ} : n.primeFactors.Nonempty ↔ 1 < n := by
  rw [←not_iff_not]
  simp only [Finset.not_nonempty_iff_eq_empty, primeFactors_eq_empty, not_lt]
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => simp

theorem eq_ideal_span_int (I : Ideal ℤ) (k : ℕ) (w : k ≠ 0) :
    I = Ideal.span {(k : ℤ)} ↔
      (k : ℤ) ∈ I ∧ ∀ q ∈ Nat.primeFactors k, (k / q : Int) ∉ I := by
  have : ∃ j : ℕ, Ideal.span {(j : ℤ)} = I :=
    ⟨(Submodule.IsPrincipal.generator I).natAbs, by rw [Int.span_natAbs, I.span_singleton_generator]⟩
  obtain ⟨j, rfl⟩ := this
  constructor
  · intro h
    rw [h]
    refine ⟨Ideal.mem_span_singleton_self (k : ℤ), fun q hq ↦ ?_⟩
    rw [Ideal.mem_span_singleton]
    norm_cast
    have hq' : 1 < q := (Nat.prime_of_mem_primeFactors hq).one_lt
    have : k / q < k := Nat.div_lt_self (Nat.pos_of_ne_zero w) hq'
    intro hk
    apply Nat.le_of_dvd at hk
    · exact irrefl k (hk.trans_lt this)
    · have := Nat.div_dvd_of_dvd <| Nat.dvd_of_mem_primeFactors hq
      exact Nat.pos_of_dvd_of_pos this (Nat.zero_lt_of_lt ‹_›)
  · rintro ⟨hk, h⟩
    simp_rw [Ideal.mem_span_singleton] at h hk
    norm_cast at h hk
    simp only [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs, Int.natAbs_cast]
    apply eq_of_le_of_not_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero w) hk) fun hj ↦ ?_
    have hj' : j ∈ k.properDivisors := by simpa only [Nat.mem_properDivisors] using ⟨hk, hj⟩
    obtain ⟨m, hm_one, hm⟩ := (Nat.mem_properDivisors_iff_exists w).mp hj'
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hm_one |>.bex
    have hp' := Nat.primeFactors_mono ⟨j, mul_comm j m ▸ hm⟩ w hp
    apply h p hp'
    use m / p
    apply Nat.mul_right_cancel (Nat.pos_of_mem_primeFactors hp)
    rwa [mul_assoc, Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp),
      Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp')]

theorem eq_zmultiples_int (G : AddSubgroup ℤ) (k : ℕ) (w : k ≠ 0) :
    G = .zmultiples (k : ℤ) ↔
      ((k : ℤ) ∈ G ∧ ∀ q ∈ Nat.primeFactors k, (k / q : Int) ∉ G) := by
  rw [← (AddSubgroup.toIntSubmodule (M := ℤ)).injective.eq_iff]
  rw [AddSubgroup.toIntSubmodule_zmultiples]
  simp_rw [←SetLike.mem_coe, ← AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe]
  exact eq_ideal_span_int _ k w

---

theorem isPrimitiveRoot_iff_eq_orderOf {R : Type*} [CommMonoid R] (a : R) :
    IsPrimitiveRoot a k ↔ k = orderOf a := by
  constructor
  · exact IsPrimitiveRoot.eq_orderOf
  · rintro rfl
    exact IsPrimitiveRoot.orderOf a

@[simps]
def zpowMulHom {G} [Group G] (g : G) : (Multiplicative ℤ) →* G where
  toFun i := g^(Multiplicative.toAdd i)
  map_one' := by simp
  map_mul' := by simp [zpow_add]

namespace AddSubgroup

def ofMultiplicative {G} [AddGroup G] (Z : Subgroup (Multiplicative G)) :
    AddSubgroup G where
  carrier := Multiplicative.toAdd '' Z.carrier
  zero_mem' := by simpa using Z.one_mem
  add_mem' ma mb := by
    simp at ma mb
    have := Z.mul_mem ma mb
    simp_all
  neg_mem' m := by
    simp at m
    have := Z.inv_mem m
    simp_all

@[simp] theorem mem_ofMultiplicative {G} [AddGroup G]
    (Z : Subgroup (Multiplicative G)) (x : G) :
    x ∈ ofMultiplicative Z ↔ (Multiplicative.ofAdd x) ∈ Z := by
  simp [ofMultiplicative]

def exponents {G} [Group G] (g : G) : AddSubgroup ℤ :=
  .ofMultiplicative (zpowMulHom g).ker

theorem mem_exponents_iff {G} [Group G] (g : G) (i : ℤ) :
    i ∈ exponents g ↔ g ^ i = 1 := by
  simp [exponents, MonoidHom.mem_ker]

@[simp] theorem zmultiples_coe_nat_inj {a b : ℕ} :
    zmultiples (a : ℤ) = zmultiples (b : ℤ) ↔ a = b := by
  constructor
  · intro h
    simp [SetLike.ext_iff] at h
    apply Nat.dvd_antisymm
    · specialize h (b : ℤ)
      simp [mem_zmultiples_iff] at h
      sorry -- easy
    · sorry -- repeat the same
  · rintro rfl
    rfl

end AddSubgroup

open AddSubgroup

theorem exponents_eq_zmultiples_orderOf {G} [Group G] (g : G) :
    exponents g = zmultiples (orderOf g : Int) := sorry

theorem IsPrimitiveRoot_iff_exponents_eq {G : Type*} [CommGroup G] (a : G) :
    IsPrimitiveRoot a k ↔ exponents a = zmultiples (k : Int) := by
  simp [isPrimitiveRoot_iff_eq_orderOf]
  simp [exponents_eq_zmultiples_orderOf]
  exact eq_comm

theorem IsPrimitiveRoot_zmod_p_iff {p : ℕ} [Fact (p.Prime)] (a : (ZMod p)ˣ) :
    IsPrimitiveRoot a (p - 1) ↔ ∀ q ∈ Nat.primeFactors (p - 1), a ^ ((p - 1) / q) ≠ 1 := by
  simp only [IsPrimitiveRoot_iff_exponents_eq]
  have h : p - 1 ≠ 0 := sorry
  simp only [eq_zmultiples_int _ _ h]
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
