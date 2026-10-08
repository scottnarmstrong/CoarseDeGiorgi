module

public import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesDefs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Summing the discounted scale profile of a cylinder

The summed bound `e.sharpness.cylinder.discount`: the square roots of the discounted scale profile
`3^{-2kb} φ_k` of a cylinder of radius `e` add up to at most `C e^{ν/2}`.
-/

@[expose] public section

open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

/-- The `k`-th term: the square root of the discounted scale profile of a cylinder of radius `e`. -/
noncomputable def discountedRoot (n : ℕ) (v b e : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) * cylinderPhi n v e k)

theorem discountedRoot_nonneg (n : ℕ) (v b e : ℝ) (k : ℕ) : 0 ≤ discountedRoot n v b e k :=
  Real.sqrt_nonneg _

private theorem triadic_eq (k : ℕ) : (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, zpow_neg, zpow_natCast]

/-- Closed form of the term in terms of the side `s = 3^{-k}`. -/
private theorem discountedRoot_eq (n : ℕ) {v b e : ℝ} (he : 0 < e) (k : ℕ) :
    discountedRoot n v b e k =
      Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) b *
        (Real.rpow e ((n : ℝ) / 2) *
          Real.rpow (max e ((3 : ℝ) ^ (-(k : ℤ)))) (-((n : ℝ) * (1 - 1 / v)) / 2)) := by
  have hs : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hM : 0 < max e ((3 : ℝ) ^ (-(k : ℤ))) := lt_max_of_lt_left he
  have h3 : Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) =
      Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) (2 * b) := by
    rw [triadic_eq]
    change (3 : ℝ) ^ (-((2 : ℝ) * (k : ℝ) * b)) = ((3 : ℝ) ^ (-(k : ℝ))) ^ (2 * b)
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  unfold discountedRoot cylinderPhi
  rw [h3, Real.sqrt_eq_rpow]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hs.le, ← Real.rpow_mul he.le, ← Real.rpow_mul hM.le]
  congr 2 <;> ring_nf

/-- Fine scales: `e ≤ 3^{-k}`. -/
private theorem root_fine (n : ℕ) {v b e ν : ℝ} (he : 0 < e) (hv : 1 ≤ v)
    (hνb : ν ≤ (n : ℝ) / v + 2 * b) (k : ℕ) (hk : e ≤ (3 : ℝ) ^ (-(k : ℤ))) :
    discountedRoot n v b e k ≤
      Real.rpow e ((n : ℝ) / 2) * Real.rpow ((3 : ℝ) ^ k) (((n : ℝ) - ν) / 2) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  set s : ℝ := (3 : ℝ) ^ (-(k : ℤ)) with hsdef
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
  rw [discountedRoot_eq n he, max_eq_right hk]
  have hinv : (3 : ℝ) ^ k = s⁻¹ := by
    rw [hsdef, zpow_neg, zpow_natCast, inv_inv]
  simp only [Real.rpow_eq_pow]
  rw [hinv, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
  have hexp : b + (-((n : ℝ) * (1 - 1 / v)) / 2) ≥ -(((n : ℝ) - ν) / 2) := by
    have : (n : ℝ) / v = (n : ℝ) - (n : ℝ) * (1 - 1 / v) := by
      field_simp
      ring
    linarith
  have hle : Real.rpow s (-(((n : ℝ) - ν) / 2)) ≥
      Real.rpow s (b + (-((n : ℝ) * (1 - 1 / v)) / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp
  simp only [Real.rpow_eq_pow] at hle
  have hen : 0 ≤ e ^ ((n : ℝ) / 2) := Real.rpow_nonneg he.le _
  calc
    _ = e ^ ((n : ℝ) / 2) * s ^ (b + (-((n : ℝ) * (1 - 1 / v)) / 2)) := by
      rw [Real.rpow_add hs]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hen

/-- Coarse scales: `3^{-k} < e`. -/
private theorem root_coarse (n : ℕ) {v b e : ℝ} (he : 0 < e) (hv : 1 ≤ v) (k : ℕ)
    (hk : (3 : ℝ) ^ (-(k : ℤ)) < e) :
    discountedRoot n v b e k =
      Real.rpow e ((n : ℝ) / (2 * v)) * Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) b := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  rw [discountedRoot_eq n he, max_eq_left hk.le]
  simp only [Real.rpow_eq_pow]
  have : e ^ ((n : ℝ) / 2) * e ^ (-((n : ℝ) * (1 - 1 / v)) / 2) =
      e ^ ((n : ℝ) / (2 * v)) := by
    rw [← Real.rpow_add he]
    congr 1
    field_simp
    ring
  rw [mul_comm, ← this]

/-- A scale `K` with `3^K e ≤ 1 < 3^{K+1} e`. -/
private theorem exists_scale {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    ∃ K : ℕ, (3 : ℝ) ^ K * e ≤ 1 ∧ 1 < (3 : ℝ) ^ (K + 1) * e := by
  have hex : ∃ k : ℕ, 1 < (3 : ℝ) ^ k * e := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / e) (by norm_num : (1 : ℝ) < 3)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ he] at hk
    exact hk
  classical
  let k0 := Nat.find hex
  have hk0 : 1 < (3 : ℝ) ^ k0 * e := Nat.find_spec hex
  have hk0ne : k0 ≠ 0 := by
    intro h
    rw [h] at hk0
    simp only [pow_zero, one_mul] at hk0
    linarith
  obtain ⟨K, hK⟩ := Nat.exists_eq_succ_of_ne_zero hk0ne
  refine ⟨K, ?_, ?_⟩
  · have := Nat.find_min hex (show K < k0 by omega)
    exact not_lt.mp this
  · rw [hK] at hk0
    exact hk0

/-- The summed bound `e.sharpness.cylinder.discount` for the square roots of the discounted
profile. -/
theorem discountedRoot_sum (n : ℕ) {v b e ν : ℝ} (he : 0 < e) (he1 : e < 1) (hv : 1 ≤ v)
    (hb : 0 < b) (hνn : ν < n) (hνb : ν ≤ (n : ℝ) / v + 2 * b) :
    Summable (fun k => discountedRoot n v b e k) ∧
      ∑' k, discountedRoot n v b e k ≤
        (Real.rpow 3 (((n : ℝ) - ν) / 2) / (Real.rpow 3 (((n : ℝ) - ν) / 2) - 1) +
          1 / (1 - Real.rpow 3 (-b))) * Real.rpow e (ν / 2) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  obtain ⟨K, hK1, hK2⟩ := exists_scale he he1
  set γ : ℝ := ((n : ℝ) - ν) / 2 with hγ
  have hγpos : 0 < γ := by rw [hγ]; linarith
  set ρ : ℝ := Real.rpow 3 γ with hρ
  have hρ1 : 1 < ρ := Real.one_lt_rpow (by norm_num) hγpos
  set σ : ℝ := Real.rpow 3 (-b) with hσ
  have hσ0 : 0 < σ := Real.rpow_pos_of_pos (by norm_num) _
  have hσ1 : σ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρk : ∀ k : ℕ, Real.rpow ((3 : ℝ) ^ k) γ = ρ ^ k := by
    intro k
    rw [hρ]
    change ((3 : ℝ) ^ k) ^ γ = ((3 : ℝ) ^ γ) ^ k
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hσk : ∀ k : ℕ, Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) b = σ ^ k := by
    intro k
    rw [hσ, triadic_eq]
    change ((3 : ℝ) ^ (-(k : ℝ))) ^ b = ((3 : ℝ) ^ (-b)) ^ k
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  let A : ℝ := Real.rpow e ((n : ℝ) / 2)
  let B : ℝ := Real.rpow e ((n : ℝ) / (2 * v))
  have hA : 0 ≤ A := Real.rpow_nonneg he.le _
  have hB : 0 ≤ B := Real.rpow_nonneg he.le _
  let g : ℕ → ℝ := fun k => if K < k then σ ^ k else 0
  let h1 : ℕ → ℝ := fun k => if k ≤ K then A * ρ ^ k else 0
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    dsimp only [g]; split_ifs <;> positivity
  have hgs : Summable g :=
    Summable.of_nonneg_of_le hg0 (fun k => by
      dsimp only [g]; split_ifs
      · exact le_rfl
      · positivity) (summable_geometric_of_lt_one hσ0.le hσ1)
  have hh1s : Summable h1 := summable_of_ne_finset_zero (s := Finset.range (K + 1)) (fun k hk => by
    have : ¬ k ≤ K := by
      intro h; exact hk (Finset.mem_range.mpr (by omega))
    simp [h1, this])
  have hbound : ∀ k, discountedRoot n v b e k ≤ h1 k + B * g k := by
    intro k
    by_cases hk : k ≤ K
    · have hfine : e ≤ (3 : ℝ) ^ (-(k : ℤ)) := by
        have : (3 : ℝ) ^ k * e ≤ 1 :=
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) he.le).trans hK1
        rw [zpow_neg, zpow_natCast]
        rw [le_inv_comm₀ he (by positivity)]
        rw [inv_eq_one_div, le_div_iff₀ he]
        nlinarith
      have := root_fine n he hv hνb k hfine
      have e2 : Real.rpow ((3 : ℝ) ^ k) (((n : ℝ) - ν) / 2) = ρ ^ k := hρk k
      have hgz : g k = 0 := by simp [g, not_lt.mpr hk]
      have h1v : h1 k = A * ρ ^ k := by simp [h1, hk]
      rw [hgz, h1v, mul_zero, add_zero]
      calc _ ≤ _ := this
        _ = A * ρ ^ k := by rw [e2]
    · have hk' : K < k := not_le.mp hk
      have hcoarse : (3 : ℝ) ^ (-(k : ℤ)) < e := by
        have : 1 < (3 : ℝ) ^ k * e :=
          hK2.trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk') he.le)
        rw [zpow_neg, zpow_natCast, inv_lt_comm₀ (by positivity) he, inv_eq_one_div,
          div_lt_iff₀ he]
        nlinarith
      rw [root_coarse n he hv k hcoarse, hσk]
      have h1z : h1 k = 0 := by simp [h1, hk]
      have hgv : g k = σ ^ k := by simp [g, hk']
      rw [h1z, hgv, zero_add, mul_comm]
  have hsum : Summable (fun k => h1 k + B * g k) := hh1s.add (hgs.mul_left B)
  have hsumT : Summable (fun k => discountedRoot n v b e k) :=
    Summable.of_nonneg_of_le (discountedRoot_nonneg n v b e) hbound hsum
  refine ⟨hsumT, ?_⟩
  have hT : ∑' k, discountedRoot n v b e k ≤ ∑' k, h1 k + B * ∑' k, g k := by
    rw [← tsum_mul_left, ← hh1s.tsum_add (hgs.mul_left B)]
    exact hsumT.tsum_le_tsum hbound hsum
  -- the two series
  have hρne : ρ - 1 ≠ 0 := (sub_pos.mpr hρ1).ne'
  have hS1 : ∑' k, h1 k = A * ((ρ ^ (K + 1) - 1) / (ρ - 1)) := by
    rw [tsum_eq_sum (s := Finset.range (K + 1)) (fun k hk => by
      have : ¬ k ≤ K := by
        intro h; exact hk (Finset.mem_range.mpr (by omega))
      simp [h1, this])]
    rw [← geom_sum_eq hρ1.ne', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have : k ≤ K := by have := Finset.mem_range.mp hk; omega
    simp [h1, this]
  have hS2 : ∑' k, g k = σ ^ (K + 1) / (1 - σ) := by
    rw [← hgs.sum_add_tsum_nat_add (K + 1)]
    have h0 : ∑ i ∈ Finset.range (K + 1), g i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : ¬ K < i := by have := Finset.mem_range.mp hi; omega
      simp [g, this]
    rw [h0, zero_add]
    have : ∀ i, g (i + (K + 1)) = σ ^ (K + 1) * σ ^ i := by
      intro i
      have : K < i + (K + 1) := by omega
      simp only [g, this, ite_true]
      rw [pow_add]; ring
    simp_rw [this]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hσ0.le hσ1]
    field_simp
  -- estimates
  have hρK : ρ ^ K ≤ Real.rpow e (-γ) := by
    rw [← hρk K]
    have h3 : (3 : ℝ) ^ K ≤ e⁻¹ := by
      rw [← one_div, le_div_iff₀ he]
      exact hK1
    calc _ ≤ Real.rpow e⁻¹ γ := Real.rpow_le_rpow (by positivity) h3 hγpos.le
      _ = _ := by
        simp only [Real.rpow_eq_pow]
        rw [Real.inv_rpow he.le, ← Real.rpow_neg he.le]
  have hT1 : ∑' k, h1 k ≤ ρ / (ρ - 1) * Real.rpow e (ν / 2) := by
    rw [hS1]
    have hApos : A * ρ ^ K * ρ ≤ A * Real.rpow e (-γ) * ρ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρK hA) (by positivity)
    have hAe : A * Real.rpow e (-γ) = Real.rpow e (ν / 2) := by
      change Real.rpow e ((n : ℝ) / 2) * Real.rpow e (-γ) = _
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add he]
      congr 1
      rw [hγ]; ring
    calc A * ((ρ ^ (K + 1) - 1) / (ρ - 1))
        ≤ A * (ρ ^ (K + 1) / (ρ - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hρ1).le
      _ = (A * ρ ^ K * ρ) / (ρ - 1) := by rw [pow_succ]; ring
      _ ≤ (A * Real.rpow e (-γ) * ρ) / (ρ - 1) :=
          div_le_div_of_nonneg_right hApos (sub_pos.mpr hρ1).le
      _ = _ := by rw [hAe]; ring
  have hσK : σ ^ (K + 1) ≤ Real.rpow e b := by
    rw [← hσk (K + 1)]
    have h4 : (3 : ℝ) ^ (-(((K + 1 : ℕ) : ℤ))) ≤ e := by
      rw [zpow_neg, zpow_natCast, inv_le_comm₀ (by positivity) he, inv_eq_one_div,
        div_le_iff₀ he]
      nlinarith
    exact Real.rpow_le_rpow (by positivity) h4 hb.le
  have hBe : B * Real.rpow e b ≤ Real.rpow e (ν / 2) := by
    change Real.rpow e ((n : ℝ) / (2 * v)) * Real.rpow e b ≤ _
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add he]
    apply Real.rpow_le_rpow_of_exponent_ge he he1.le
    have : (n : ℝ) / (2 * v) = ((n : ℝ) / v) / 2 := by field_simp
    rw [this]
    linarith
  have hT2 : B * ∑' k, g k ≤ 1 / (1 - σ) * Real.rpow e (ν / 2) := by
    rw [hS2]
    have h1σ : 0 < 1 - σ := sub_pos.mpr hσ1
    have e1 : B * (σ ^ (K + 1) / (1 - σ)) = (B * σ ^ (K + 1)) / (1 - σ) := by ring
    have e2 : (B * σ ^ (K + 1)) / (1 - σ) ≤ (B * Real.rpow e b) / (1 - σ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσK hB) h1σ.le
    have e3 : (B * Real.rpow e b) / (1 - σ) ≤ Real.rpow e (ν / 2) / (1 - σ) :=
      div_le_div_of_nonneg_right hBe h1σ.le
    have e4 : Real.rpow e (ν / 2) / (1 - σ) = 1 / (1 - σ) * Real.rpow e (ν / 2) := by ring
    linarith
  refine hT.trans ?_
  have hfin := add_le_add hT1 hT2
  linarith

end CoarseDeGiorgi.SharpnessExamples
