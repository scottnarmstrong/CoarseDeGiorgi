module

public import CoarseDeGiorgi.Assembly.HybridEmbedding
public import CoarseDeGiorgi.Assembly.HybridRadius

@[expose] public section

namespace CoarseDeGiorgi.Assembly

open Homogenization MeasureTheory Set CoarseDeGiorgi.Localization
open scoped ENNReal

/-- Inner localization transfers the global Sobolev bound to the inner cube.
Agreement follows from the proved partition neighborhood, not an extra premise. -/
theorem hybrid_inner_critical_norm {d : ℕ} {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 1 ≤ r) (hcrit : α * r < d) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧
      ∀ (ρ R δ : ℝ) (m : ℤ),
        LocalizationCover m {x : Vec d | ∀ i, |x i| ≤ ρ / 2} R δ →
      ∀ w : Vec d → ℝ, Measurable w → ∀ L : ℝ≥0∞,
        fracSeminorm univ α r
          (localizedFunction m (coverIndices m {x : Vec d | ∀ i, |x i| ≤ ρ / 2}) w) ≤ L →
        eLpNorm w (ENNReal.ofReal (dnpvCriticalExponent d α r))
          (volume.restrict (radiusCube ρ)) ≤ C * L := by
  obtain ⟨C, hC0, hC, hbound⟩ := hybrid_compact_embedding hα hα1 hr hcrit
  refine ⟨C, hC0, hC, ?_⟩
  intro ρ R δ m hcover w hw L hL
  let K : Set (Vec d) := {x | ∀ i, |x i| ≤ ρ / 2}
  let F := localizedFunction m (coverIndices m K) w
  obtain ⟨U, hU, hKU, hEq⟩ := localizedFunction_eq_on_neighborhood hcover w
  have hcube : MeasurableSet (radiusCube (d := d) ρ) := by
    apply IsOpen.measurableSet
    simp only [radiusCube, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i |>.abs) continuous_const
  have hAE : w =ᵐ[volume.restrict (radiusCube ρ)] F := by
    filter_upwards [ae_restrict_mem hcube] with x hx
    exact (hEq (hKU (fun i => (hx i).le))).symm
  calc
    _ = eLpNorm F (ENNReal.ofReal (dnpvCriticalExponent d α r))
        (volume.restrict (radiusCube ρ)) := eLpNorm_congr_ae hAE
    _ ≤ eLpNorm F (ENNReal.ofReal (dnpvCriticalExponent d α r)) volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ C * fracSeminorm univ α r F :=
      hbound F (measurable_localizedFunction m (coverIndices m K) hw)
        (localizedFunction_compactly_supported hcover w).1
    _ ≤ C * L := mul_le_mul_right hL C

end CoarseDeGiorgi.Assembly
