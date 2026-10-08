module

public import CoarseDeGiorgi.Localization.Lipschitz
public import CoarseDeGiorgi.Localization.SparseSum

/-! # Compact-localization sum estimate using the fractional norms `fracNorm`

No lower-fractional theorem is imported. The local membership and eventual
energy estimate enter explicitly in the conditional consumer.
-/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Foundations
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

/-- The global sum is already the zero extension because every multiplier is supported inside. -/
def localizedFunction (m : ℤ) (Z : Finset (Fin d → ℤ)) (w : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ z ∈ Z, localizationPartition m Z z x * w x

theorem localizedFunction_eq_on_partition {m : ℤ} {Z : Finset (Fin d → ℤ)} {x : Vec d}
    (hx : (∑ z ∈ Z, localizationPartition m Z z x) = 1) (w : Vec d → ℝ) :
    localizedFunction m Z w x = w x := by
  rw [localizedFunction, ← Finset.sum_mul, hx, one_mul]

theorem support_partition_subset_auxCube (m : ℤ) (Z : Finset (Fin d → ℤ)) (z : Fin d → ℤ) :
    Function.support (localizationPartition m Z z) ⊆ auxCube m z := by
  intro x hx
  by_contra hn
  have h := localizationPartition_separation (subset_tsupport _ hx) hn
  rw [Euclid.eDist2_self] at h
  exact (not_le_of_gt (half_pos (gridSpacing_pos m))) h

theorem localizationPartition_mul_eq_cutoff (m : ℤ) (Z : Finset (Fin d → ℤ))
    (z : Fin d → ℤ) (w : Vec d → ℝ) :
    (fun x => localizationPartition m Z z x * w x) =
      FracGeometry.cutoffExtension (auxCube m z) (localizationPartition m Z z) w :=
  (FracGeometry.cutoffExtension_eq_mul (support_partition_subset_auxCube m Z z)).symm

theorem measurable_localizedFunction (m : ℤ) (Z : Finset (Fin d → ℤ))
    {w : Vec d → ℝ} (hw : Measurable w) : Measurable (localizedFunction m Z w) :=
  Finset.measurable_sum Z fun z _ => (contDiff_localizationPartition m Z z).continuous.measurable.mul hw

theorem card_filter_partition_mul_ne_zero_le (m : ℤ) (Z : Finset (Fin d → ℤ))
    (w : Vec d → ℝ) (x : Vec d) :
    (Z.filter fun z => localizationPartition m Z z x * w x ≠ 0).card ≤ 4 ^ d := by
  apply le_trans _ (card_filter_bump_ne_zero_le m Z x)
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzZ, hn⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzZ, support_localizationPartition_subset m Z z (mul_ne_zero_iff.mp hn).1⟩

/-- First inequality of (e.localization.sum), with a constant depending only on dimension and r. -/
theorem localizedFunction_norm_rpow_le {r α : ℝ} (hr : 1 < r) (m : ℤ)
    (Z : Finset (Fin d → ℤ)) {w : Vec d → ℝ} (hw : Measurable w) :
    fracNorm univ α r (localizedFunction m Z w) ^ r ≤
      ENNReal.ofReal ((2 * 4 ^ d : ℕ) ^ (r - 1 : ℝ)) *
        ∑ z ∈ Z, fracNorm univ α r (fun x => localizationPartition m Z z x * w x) ^ r := by
  exact fracNorm_sum_rpow_le_of_overlap hr Z _
    (fun z _ => (contDiff_localizationPartition m Z z).continuous.measurable.mul hw)
    (card_filter_partition_mul_ne_zero_le m Z w)

/-- Two-term convex power bound, valid in the extended nonnegative reals. -/
theorem ennreal_add_rpow_le {r : ℝ} (hr : 1 ≤ r) (a b : ℝ≥0∞) :
    (a + b) ^ r ≤ (2 : ℝ≥0∞) ^ (r - 1) * (a ^ r + b ^ r) := by
  have hh := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset Bool)
    (fun t => if t then a else b) hr
  simpa only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, Finset.card_univ,
    Fintype.card_bool, Nat.cast_ofNat, add_comm] using hh


/-- The fractional cutoff estimate (`l.fractional.cutoff`), stated with `fracNorm` and
`fracSeminorm` raised to the power `r`. -/
theorem exists_cutoff_power_constant [NeZero d] {α r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ 0 < A ∧
      ∀ (V : Set (Vec d)), IsOpen V → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (φ w : Vec d → ℝ), (∀ x, |φ x| ≤ 1) →
      (∀ x y, |φ x - φ y| ≤ Euclid.eDist2 x y / ε) →
      (∀ x ∈ Function.support φ, ∀ y ∉ V, ε ≤ Euclid.eDist2 x y) →
      Measurable w → fracNorm V α r w < ⊤ →
      fracNorm univ α r (FracGeometry.cutoffExtension V φ w) ^ r ≤
        A * (fracSeminorm V α r w ^ r + ENNReal.ofReal (ε ^ (-α * r)) *
          eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ^ r) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨C, hC, hcut⟩ := FracGeometry.fractional_cutoff (d := d) hα0 hα1 hr
  let A : ℝ≥0∞ := ENNReal.ofReal C ^ r * (2 : ℝ≥0∞) ^ (r - 1)
  refine ⟨A, by dsimp [A]; finiteness, by dsimp [A]; positivity, ?_⟩
  intro V hV ε hε hε1 φ w hBound hLip hSep hw hfin
  have hh := hcut V hV ε hε hε1 φ w hBound hLip hSep hw hfin
  change fracNorm univ α r (FracGeometry.cutoffExtension V φ w) ≤ ENNReal.ofReal C *
    (fracSeminorm V α r w + ENNReal.ofReal (ε ^ (-α)) * eLpNorm w (ENNReal.ofReal r) (volume.restrict V)) at hh
  have hpower := ENNReal.rpow_le_rpow hh hr0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le] at hpower
  have htwo := ennreal_add_rpow_le hr.le (fracSeminorm V α r w)
    (ENNReal.ofReal (ε ^ (-α)) * eLpNorm w (ENNReal.ofReal r) (volume.restrict V))
  have hscale : (ENNReal.ofReal (ε ^ (-α)) * eLpNorm w (ENNReal.ofReal r) (volume.restrict V)) ^ r =
      ENNReal.ofReal (ε ^ (-α * r)) * eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ^ r := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hε.le _) hr0.le, ← Real.rpow_mul hε.le]
  rw [hscale] at htwo
  exact hpower.trans (by simpa only [A, mul_assoc] using mul_le_mul_right htwo (ENNReal.ofReal C ^ r))

/-- The uniform partition constant chooses a single admissible cutoff scale. -/
theorem exists_partition_cutoff_scale : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
    ∀ (m : ℤ) (Z : Finset (Fin d → ℤ)) (z : Fin d → ℤ) (x y : Vec d),
      |localizationPartition m Z z x - localizationPartition m Z z y| ≤
        Euclid.eDist2 x y / (c * gridSpacing m) := by
  obtain ⟨C, hC, hLip⟩ := exists_localizationPartition_difference_bound (d := d)
  let c : ℝ := 1 / (2 * (C + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcHalf : c ≤ 1 / 2 := by
    dsimp only [c]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (C + 1)) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith only [hC]
  refine ⟨c, hc, hcHalf, ?_⟩
  intro m Z z x y
  have h := hLip m Z z x y
  have hratio : C / gridSpacing m ≤ (c * gridSpacing m)⁻¹ := by
    have he : (c * gridSpacing m)⁻¹ = (2 * (C + 1)) / gridSpacing m := by
      dsimp only [c]
      simp only [one_div, mul_inv_rev, inv_inv]
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith only [hC]) (gridSpacing_pos m).le
  calc
    _ ≤ (C / gridSpacing m) * Euclid.eDist2 x y := h
    _ ≤ (c * gridSpacing m)⁻¹ * Euclid.eDist2 x y :=
      mul_le_mul_of_nonneg_right hratio (Euclid.eDist2_nonneg _ _)
    _ = _ := by ring

/-- The complete (e.localization.sum) bound. Local fractional membership is explicit;
the per-cube lower energy bound is consumed in a separate conditional theorem. -/
theorem exists_localization_sum_constant [NeZero d] {α r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ 0 < C ∧
      ∀ (m : ℤ), gridSpacing m ≤ 1 → ∀ (Z : Finset (Fin d → ℤ))
      (w : Vec d → ℝ), Measurable w → (∀ z ∈ Z, fracNorm (auxCube m z) α r w < ⊤) →
      fracNorm univ α r (localizedFunction m Z w) ^ r ≤
        C * (∑ z ∈ Z, fracSeminorm (auxCube m z) α r w ^ r) +
          C * ENNReal.ofReal (gridSpacing m ^ (-α * r)) *
            ∑ z ∈ Z, eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ^ r := by
  obtain ⟨A, hAfin, hApos, hcut⟩ := exists_cutoff_power_constant (d := d) hα0 hα1 hr
  obtain ⟨c, hc, hcHalf, hLip⟩ := exists_partition_cutoff_scale (d := d)
  let B : ℝ≥0∞ := ENNReal.ofReal (c ^ (-α * r))
  let D : ℝ≥0∞ := ENNReal.ofReal ((2 * 4 ^ d : ℕ) ^ (r - 1 : ℝ))
  let C : ℝ≥0∞ := D * A * (1 + B)
  have hCfin : C ≠ ⊤ := by dsimp [C, D, B]; finiteness
  have hCpos : 0 < C := by dsimp [C, D]; positivity
  refine ⟨C, hCfin, hCpos, ?_⟩
  intro m hs1 Z w hw hfin
  have hε : 0 < c * gridSpacing m := mul_pos hc (gridSpacing_pos m)
  have hε1 : c * gridSpacing m ≤ 1 := by nlinarith only [hcHalf, hs1, hc, gridSpacing_pos m]
  have hterm (z : Fin d → ℤ) (hz : z ∈ Z) :
      fracNorm univ α r (fun x => localizationPartition m Z z x * w x) ^ r ≤
        A * (fracSeminorm (auxCube m z) α r w ^ r +
          B * ENNReal.ofReal (gridSpacing m ^ (-α * r)) *
            eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ^ r) := by
    rw [localizationPartition_mul_eq_cutoff]
    have hh := hcut (auxCube m z) (isOpen_auxCube m z) (c * gridSpacing m) hε hε1
      (localizationPartition m Z z) w (localizationPartition_bound hz) (hLip m Z z)
      (fun x hx y hy => (mul_le_mul_of_nonneg_right hcHalf (gridSpacing_pos m).le).trans
        (by simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using localizationPartition_separation (subset_tsupport _ hx) hy)) hw (hfin z hz)
    rw [Real.mul_rpow hc.le (gridSpacing_pos m).le, ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)] at hh
    exact hh
  have hsum := localizedFunction_norm_rpow_le (α := α) hr m Z hw
  have hterms := Finset.sum_le_sum hterm
  have hDA : D * A ≤ C := by dsimp only [C]; exact le_mul_of_one_le_right' (le_add_right le_rfl)
  have hDAB : D * A * B ≤ C := by dsimp only [C]; exact mul_le_mul_right (le_add_left le_rfl) (D * A)
  calc
    _ ≤ D * ∑ z ∈ Z, fracNorm univ α r (fun x => localizationPartition m Z z x * w x) ^ r := hsum
    _ ≤ D * ∑ z ∈ Z, A * (fracSeminorm (auxCube m z) α r w ^ r +
        B * ENNReal.ofReal (gridSpacing m ^ (-α * r)) *
          eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ^ r) := mul_le_mul_right hterms D
    _ = (D * A) * (∑ z ∈ Z, fracSeminorm (auxCube m z) α r w ^ r) +
        (D * A * B) * ENNReal.ofReal (gridSpacing m ^ (-α * r)) *
          ∑ z ∈ Z, eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ^ r := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
    _ ≤ _ := add_le_add (by
      simpa only [mul_comm] using mul_le_mul_right hDA (∑ z ∈ Z, fracSeminorm (auxCube m z) α r w ^ r)) (by
      have h := mul_le_mul_right hDAB
        (ENNReal.ofReal (gridSpacing m ^ (-α * r)) *
          ∑ z ∈ Z, eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ^ r)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h)

end
end CoarseDeGiorgi.Localization
