import CoarseDeGiorgi.Foundations.FracGeometry.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- The literal zero extension of a product defined on the open domain. -/
def cutoffExtension (V : Set (Vec d)) (φ w : Vec d → ℝ) : Vec d → ℝ :=
  V.indicator (fun x => φ x * w x)

/-- The explicit Euclidean Lipschitz condition also supplies continuity. -/
theorem continuous_of_euclid_lipschitz {ε : ℝ} (hε : 0 < ε) {φ : Vec d → ℝ}
    (hLip : ∀ x y, |φ x - φ y| ≤ euclidDist x y / ε) : Continuous φ := by
  let K : ℝ≥0 := ⟨Real.sqrt (d : ℝ) / ε, div_nonneg (Real.sqrt_nonneg _) hε.le⟩
  have h : LipschitzWith K φ := LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq]
    calc
      |φ x - φ y| ≤ euclidDist x y / ε := hLip x y
      _ ≤ (Real.sqrt (d : ℝ) * dist x y) / ε :=
        div_le_div_of_nonneg_right (by
          rw [euclidDist_eq_eDist2]
          exact Euclid.eDist2_le_sqrt_mul_dist x y) hε.le
      _ = (K : ℝ) * dist x y := by
        change Real.sqrt (d : ℝ) * dist x y / ε = (Real.sqrt (d : ℝ) / ε) * dist x y
        ring
  exact h.continuous

/-- The indicator agrees with the global product when its multiplier is supported inside. -/
theorem cutoffExtension_eq_mul {V : Set (Vec d)} {φ w : Vec d → ℝ}
    (hSupport : Function.support φ ⊆ V) :
    cutoffExtension V φ w = fun x => φ x * w x := by
  funext x
  by_cases hx : x ∈ V
  · exact Set.indicator_of_mem hx _
  · have hφ : φ x = 0 := by
      by_contra hne
      exact hx (hSupport hne)
    simp only [cutoffExtension, Set.indicator_of_notMem hx, hφ, zero_mul]

theorem measurable_cutoffExtension {V : Set (Vec d)} (hV : MeasurableSet V)
    {φ w : Vec d → ℝ} (hφ : Measurable φ) (hw : Measurable w) :
    Measurable (cutoffExtension V φ w) :=
  (hφ.mul hw).indicator hV

/-- The source's zero extension has an `L^r` bound with constant one. -/
theorem eLpNorm_cutoffExtension_le {V : Set (Vec d)} (hV : IsOpen V)
    {φ w : Vec d → ℝ} (hφ : Measurable φ) (hw : Measurable w)
    (hBound : ∀ x, |φ x| ≤ 1) (p : ℝ≥0∞) :
    eLpNorm (cutoffExtension V φ w) p volume ≤ eLpNorm w p (volume.restrict V) := by
  unfold cutoffExtension
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hV.measurableSet]
  apply eLpNorm_mono (hφ.mul hw).aestronglyMeasurable
  intro x
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hBound x) (abs_nonneg (w x))

/-- The multiplier difference has the two bounds used by the source proof. -/
theorem cutoff_difference_le_min {φ : Vec d → ℝ} {ε : ℝ}
    (hBound : ∀ x, |φ x| ≤ 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ euclidDist x y / ε) (x y : Vec d) :
    |φ x - φ y| ≤ min 2 (euclidDist x y / ε) := by
  apply le_min
  · calc
      |φ x - φ y| = |φ x + -φ y| := by rw [sub_eq_add_neg]
      _ ≤ |φ x| + |-φ y| := abs_add_le _ _
      _ ≤ 2 := by rw [abs_neg]; linarith only [hBound x, hBound y]
  · exact hLip x y

/-- The precise interior decomposition before taking powers or integrating. -/
theorem cutoff_product_difference_le {φ : Vec d → ℝ} {ε : ℝ}
    (hBound : ∀ x, |φ x| ≤ 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ euclidDist x y / ε)
    (w : Vec d → ℝ) (x y : Vec d) :
    |φ x * w x - φ y * w y| ≤
      |w x - w y| + min 2 (euclidDist x y / ε) * |w y| := by
  rw [show φ x * w x - φ y * w y =
    φ x * (w x - w y) + (φ x - φ y) * w y by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  apply add_le_add
  · simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hBound x) (abs_nonneg (w x - w y))
  · exact mul_le_mul_of_nonneg_right
      (cutoff_difference_le_min hBound hLip x y) (abs_nonneg (w y))

/-- A nonnegative power-sum bound in the same carrier as the Gagliardo integrals. -/
theorem ofReal_rpow_le_power_sum {a b c r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hr : 0 < r) (h : a ≤ b + c) :
    ENNReal.ofReal (a ^ r) ≤
      (2 : ℝ≥0∞) ^ r * (ENNReal.ofReal (b ^ r) + ENNReal.ofReal (c ^ r)) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg ha hr.le,
    ← ENNReal.ofReal_rpow_of_nonneg hb hr.le,
    ← ENNReal.ofReal_rpow_of_nonneg hc hr.le]
  calc
    ENNReal.ofReal a ^ r ≤ (ENNReal.ofReal b + ENNReal.ofReal c) ^ r := by
      apply ENNReal.rpow_le_rpow _ hr.le
      rw [← ENNReal.ofReal_add hb hc]
      exact ENNReal.ofReal_le_ofReal h
    _ ≤ (2 : ℝ≥0∞) ^ r * (ENNReal.ofReal b ^ r + ENNReal.ofReal c ^ r) :=
      ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hr.le

/-- The powered interior estimate, with its two source terms still separate. -/
theorem cutoff_product_rpow_le {φ : Vec d → ℝ} {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hBound : ∀ x, |φ x| ≤ 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ euclidDist x y / ε)
    (w : Vec d → ℝ) (x y : Vec d) :
    ENNReal.ofReal (|φ x * w x - φ y * w y| ^ r) ≤
      (2 : ℝ≥0∞) ^ r *
        (ENNReal.ofReal (|w x - w y| ^ r) +
          ENNReal.ofReal ((min 2 (euclidDist x y / ε)) ^ r) *
            ENNReal.ofReal (|w y| ^ r)) := by
  have hm : 0 ≤ min 2 (euclidDist x y / ε) :=
    le_min (by norm_num) (div_nonneg (by
      rw [euclidDist_eq_eDist2]; exact Euclid.eDist2_nonneg x y) hε.le)
  have h := ofReal_rpow_le_power_sum (abs_nonneg _) (abs_nonneg _)
    (mul_nonneg hm (abs_nonneg _)) hr (cutoff_product_difference_le hBound hLip w x y)
  rwa [Real.mul_rpow hm (abs_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg hm _)] at h

end

end CoarseDeGiorgi.Foundations.FracGeometry
