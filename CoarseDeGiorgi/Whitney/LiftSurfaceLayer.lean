import CoarseDeGiorgi.Selection.SurfaceEnergy
import CoarseDeGiorgi.Whitney.LiftZeroExtension

/-! # Surface maximal control of exterior layer energy

The density version uses the summed-face surface measure `surfaceMeasure` and proves
the constant 54 of the manuscript. Cell containment is the Whitney geometry input.
-/
namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section

/-- Half the mass of a centered surface-energy interval controls the one-sided
collar. The normalization is exactly the source's coarea factor one half. -/
theorem lift_collar_energy_le_maximal {n : ℕ} {ρ R τ r : ℝ}
    (hτ : 0 ≤ τ) (hr : 0 < r)
    (hinterval : Ioo τ (τ + r) ⊆ Ioo ρ R)
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in Selection.cubicalAnnulus (n + 1) τ (τ + r), g x) ≤
      ENNReal.ofReal r * Selection.surfaceEnergyMaximal ρ R g τ := by
  have hmass : 2 * (∫⁻ x in Selection.cubicalAnnulus (n + 1) τ (τ + r), g x) ≤
      Selection.surfaceEnergyMeasure ρ R g (ball τ r) := by
    rw [← Selection.cubical_coarea hτ hg, Selection.surfaceEnergyMeasure_ball]
    apply lintegral_mono_set
    intro l hl
    refine ⟨?_, hinterval hl⟩
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith only [hl.1, hr], hl.2⟩
  have havg : Selection.surfaceEnergyMeasure ρ R g (ball τ r) ≤
      ENNReal.ofReal (2 * r) * Selection.surfaceEnergyMaximal ρ R g τ := by
    have hh : Selection.surfaceEnergyMeasure ρ R g (ball τ r) /
        ENNReal.ofReal (2 * r) ≤ Selection.surfaceEnergyMaximal ρ R g τ :=
      le_iSup_of_le r (le_iSup_of_le hr le_rfl)
    exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hr)).ne'
      ENNReal.ofReal_ne_top).mp hh |>.trans_eq (mul_comm _ _)
  have hh := hmass.trans havg
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    mul_assoc] at hh
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp hh

/-- The subsolution-layer display, for any finite disjoint family of cells in
its exterior collar. No layer energy estimate is assumed. -/
theorem lift_subsolution_layer_of_collar {n : ℕ} {ι : Type*}
    (U : ι → Set (Vec (n + 1))) (S : Finset ι)
    (hmeas : ∀ k ∈ S, MeasurableSet (U k))
    (hdisj : Set.PairwiseDisjoint (↑S) U)
    {ρ R τ : ℝ} (hτ : 0 ≤ τ) (j : ℕ)
    (hinterval : Ioo τ (τ + 54 * (3 : ℝ) ^ (-(j : ℝ))) ⊆ Ioo ρ R)
    (hcollar : ∀ k ∈ S, U k ⊆
      Selection.cubicalAnnulus (n + 1) τ (τ + 54 * (3 : ℝ) ^ (-(j : ℝ))))
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    (∑ k ∈ S, ∫⁻ x in U k, g x) ≤
      ENNReal.ofReal (54 * (3 : ℝ) ^ (-(j : ℝ))) *
        Selection.surfaceEnergyMaximal ρ R g τ := by
  rw [← lintegral_biUnion_finset hdisj hmeas]
  apply (lintegral_mono_set ?_).trans
    (lift_collar_energy_le_maximal hτ (by positivity) hinterval hg)
  exact iUnion₂_subset fun k hk => hcollar k hk

end
end CoarseDeGiorgi.Whitney
