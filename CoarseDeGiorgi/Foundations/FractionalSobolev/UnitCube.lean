import CoarseDeGiorgi.Foundations.FractionalSobolev.UnitCubeEstimate

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

/-- DNPV Theorem 6.7 on the unit cube, with exactly the statement `dnpv_theorem_6_7_unitCube`. -/
theorem dnpv_theorem_6_7_unitCube_proved :
    ∀ n : ℕ, ∀ s p : ℝ, 0 < s → s < 1 → 1 ≤ p → s * p < (n : ℝ) →
      ∃ C : ℝ, 0 < C ∧
        ∀ f : Vec n → ℝ, MemDnpvSobolev (dnpvUnitCube n) s p f →
          eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) (volume.restrict (dnpvUnitCube n)) ≤
              ENNReal.ofReal C * fracNorm (dnpvUnitCube n) s p f := by
  intro n s p hs hs1 hp hsp
  obtain ⟨C, hC, hineq⟩ := unitCubeSobolev_measurable hs hs1 hp hsp
  refine ⟨C, hC, ?_⟩
  intro f hf
  have hmeas := hf.1.aestronglyMeasurable
  let g := hmeas.mk f
  have hg : Measurable g := hmeas.measurable_mk
  have hfg : f =ᵐ[volume.restrict (dnpvUnitCube n)] g := hmeas.ae_eq_mk
  rw [eLpNorm_congr_ae hfg, fracNorm_congr_ae hfg s p]
  exact hineq g hg

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
