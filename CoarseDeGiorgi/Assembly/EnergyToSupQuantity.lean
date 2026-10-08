import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
import Mathlib.Tactic

namespace CoarseDeGiorgi.Assembly
open Homogenization MeasureTheory Aliases
open scoped ENNReal

/-- Level truncation removes a nonnegative part of the energy integrand. -/
theorem energy_to_sup_gradient_mono {d : ℕ} (a : CoeffField d)
    (u : Vec d → ℝ) (G : Vec d → Vec d) {l k ρ R : ℝ}
    (hl : l ≤ k) (hr : ρ ≤ R) :
    weightedEnergy a (originCube ρ) (positiveTruncationGradient u G k) ≤
      weightedEnergy a (originCube R) (positiveTruncationGradient u G l) := by
  apply (lintegral_mono ?_).trans (lintegral_mono_set (caccioppoli_cube_mono hr))
  intro x
  unfold positiveTruncationGradient
  dsimp only
  split_ifs with hk hll
  · exact le_rfl
  · exact False.elim (hll (lt_of_le_of_lt hl hk))
  · simp [vecDot, matVecMul]
  · exact le_rfl

/-- The two-level quantity decreases with level and increases with radius. -/
theorem energy_to_sup_quantity_mono {d : ℕ} {a : CoeffField d}
    (ha : IsWeightedCoeffOn (originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : AEStronglyMeasurable u (volume.restrict (originCube 1)))
    {l k ρ R : ℝ} (hl : l ≤ k) (hr : ρ ≤ R) (hR : R ≤ 1) :
    twoLevelQuantity a ha q t ht hq u G k ρ ≤ twoLevelQuantity a ha q t ht hq u G l R := by
  unfold twoLevelQuantity
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply add_le_add
  · apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 2)
    apply (eLpNorm_mono_measure _ (Measure.restrict_mono (caccioppoli_cube_mono hr) le_rfl)).trans
    apply eLpNorm_mono_ae
      ((show Continuous (fun z : ℝ => max (z - k) 0) from
        (continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
          (hu.mono_measure (Measure.restrict_mono (caccioppoli_cube_mono hR) le_rfl)))
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (u x - k) 0), abs_of_nonneg (le_max_right (u x - l) 0)]
    exact max_le_max (sub_le_sub_left hl _) le_rfl
  · gcongr
    exact energy_to_sup_gradient_mono a u G hl hr

/-- The value part is bounded by the combined two-level quantity. -/
theorem energy_to_sup_norm_le_quantity {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (l R : ℝ) :
    eLpNorm (fun x => max (u x - l) 0) (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube R)) ≤ twoLevelQuantity a ha q t ht hq u G l R := by
  unfold twoLevelQuantity
  dsimp only
  calc
    _ = ((eLpNorm (fun x => max (u x - l) 0) (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube R))).rpow 2).rpow (1 / 2) := by
        simp only [ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul,
          show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow (le_add_right le_rfl :
      (eLpNorm (fun x => max (u x - l) 0) (ENNReal.ofReal (paramR q))
        (volume.restrict (originCube R))).rpow 2 ≤ _) (by norm_num : (0 : ℝ) ≤ 1 / 2)

end CoarseDeGiorgi.Assembly
