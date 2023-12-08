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

@[simp] theorem mem_exponents_iff {G} [Group G] (g : G) (i : ℤ) :
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
      obtain ⟨k, h⟩ := h
      use k.natAbs
      replace h := congr_arg Int.natAbs h
      simp only [Int.natAbs_ofNat] at h
      subst h
      simp [Int.natAbs_mul, mul_comm]
    · specialize h (a : ℤ)
      simp [mem_zmultiples_iff] at h
      obtain ⟨k, h⟩ := h
      use k.natAbs
      replace h := congr_arg Int.natAbs h
      simp only [Int.natAbs_ofNat] at h
      subst h
      simp [Int.natAbs_mul, mul_comm]
  · rintro rfl
    rfl

end AddSubgroup

open AddSubgroup

theorem exponents_eq_zmultiples_orderOf {G} [Group G] (g : G) :
    exponents g = zmultiples (orderOf g : Int) := by
  ext i
  simp [mem_zmultiples_iff]
  constructor
  · intro h
    rw [← orderOf_dvd_iff_zpow_eq_one] at h
    obtain ⟨k, rfl⟩ := h
    use k
    rw [mul_comm]
  · rintro ⟨j, rfl⟩
    rw [mul_comm, zpow_mul, zpow_coe_nat, pow_orderOf_eq_one, one_zpow]

theorem IsPrimitiveRoot_iff_exponents_eq {G : Type*} [CommGroup G] (a : G) :
    IsPrimitiveRoot a k ↔ exponents a = zmultiples (k : Int) := by
  simp [isPrimitiveRoot_iff_eq_orderOf]
  simp [exponents_eq_zmultiples_orderOf]
  exact eq_comm

theorem IsPrimitiveRoot_zmod_p_iff {p : ℕ} [Fact (p.Prime)] (a : (ZMod p)ˣ) :
    IsPrimitiveRoot a (p - 1) ↔
      ∀ q ∈ Nat.primeFactors (p - 1), a ^ ((p - 1) / q) ≠ 1 := by
  simp only [IsPrimitiveRoot_iff_exponents_eq]
  have h : p - 1 ≠ 0 := by simpa using Nat.Prime.one_lt Fact.out
  simp [eq_zmultiples_int _ _ h, mem_exponents_iff,
    ZMod.units_pow_card_sub_one_eq_one]
  norm_cast
