import CoarseDeGiorgi.Localization.SummedCore
import CoarseDeGiorgi.Harnack.WeakHarnack.ApproximationBridge

/-! # Convergence of the localized functions

If the weighted norms on the unit cube tend to zero, so do the weighted norms on every
fixed cube of the cover; the continuous inclusion then gives convergence in each local
fractional norm. -/
namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d : ℕ}

theorem mean_enorm_le {Q : Set (Vec d)} (hQ : Q ⊆ originCube 1) {w : Vec d → ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict (originCube 1))) :
    ‖volumeAverage Q w‖ₑ ≤
      ENNReal.ofReal ((volume Q).toReal⁻¹) * eLpNorm w 1 (volume.restrict (originCube 1)) := by
  unfold volumeAverage
  rw [enorm_mul, Real.enorm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  refine mul_le_mul_right ?_ _
  rw [eLpNorm_one_eq_lintegral_enorm hw]
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set hQ)

theorem h1aWeightedNorm_le_add (a : CoeffField d) (Q : Set (Vec d)) (w : Vec d → ℝ)
    (G : Vec d → Vec d) :
    h1aWeightedNorm a Q w G ≤ ‖volumeAverage Q w‖ₑ + (weightedEnergy a Q G) ^ (1 / 2 : ℝ) := by
  unfold h1aWeightedNorm
  refine (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans (add_le_add_left ?_ _)
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq_eq_abs, ← Real.enorm_eq_ofReal_abs]

/-- The weighted norm on a fixed subcube tends to zero with the weighted norm on the unit cube. -/
theorem h1aWeightedNorm_cube_tendsto [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {Q : Set (Vec d)} (hQ : Q ⊆ originCube 1)
    (u : ℕ → Vec d → ℝ) (H : ℕ → Vec d → Vec d)
    (hu : ∀ j, MemH1a a (originCube 1) (u j) (H j))
    (hto : Tendsto (fun j => h1aWeightedNorm a (originCube 1) (u j) (H j)) atTop (𝓝 0)) :
    Tendsto (fun j => h1aWeightedNorm a Q (u j) (H j)) atTop (𝓝 0) := by
  obtain ⟨hL1, -⟩ := Harnack.WeakHarnack.h1aWeightedNorm_tendsto_l1_and_energy a ha u H hu hto
  have h1 : Tendsto (fun j => ENNReal.ofReal ((volume Q).toReal⁻¹) *
      eLpNorm (u j) 1 (volume.restrict (originCube 1))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hL1 (Or.inr ENNReal.ofReal_ne_top)
  have h2 : Tendsto (fun j => (weightedEnergy a Q (H j)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto (fun _ => bot_le)
      (fun j => (ENNReal.rpow_le_rpow (lintegral_mono_set hQ) (by norm_num)).trans
        (LowerFractional.lower_weighted_energy_norm_le a _ (u j) (H j)))
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le)
    (fun j => (h1aWeightedNorm_le_add a Q (u j) (H j)).trans
      (add_le_add (mean_enorm_le hQ (hu j).1) le_rfl))

end
end CoarseDeGiorgi.Localization
