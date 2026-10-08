import CoarseDeGiorgi.LowerFractional.CubeDomain
import CoarseDeGiorgi.Weighted.Identification

/-! This module supplies the W1,1 bridge used by the lower-fractional core.
The reconstruction theorem `fractional_reconstruction` discharges that interface in Final.lean. -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

/-- The reconstruction hypothesis applies to the represented H1a pairs that
already lie in Lr. Its constant keeps the quantifier order of the hypothesis. -/
theorem weighted_fractional_reconstruction_of_reconstruction
    (hreconstruction : ∀ {d : ℕ} {α r : ℝ},
      0 < α → α < 1 → 1 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (Dw : Vec d → Vec d),
          HasWeakGradientOn (auxCube m z) w Dw →
          IntegrableOn w (auxCube m z) volume →
          IntegrableOn Dw (auxCube m z) volume →
          MemLp w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) →
          fracSeminorm (auxCube m z) α r w ≤
            ENNReal.ofReal C *
              ∑' k : {k : ℤ // m ≤ k},
                ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
                  eLpNorm (fun x => euclidNorm (auxAverage m k.1 z Dw x))
                    (ENNReal.ofReal r) (volume.restrict (auxCube m z)))
    {d : ℕ} [NeZero d] {α r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (z : Fin d → ℤ) (a : CoeffField d)
      (_ha : IsWeightedCoeffOn (auxCube m z) a) (w : Vec d → ℝ) (G : Vec d → Vec d),
      MemH1a a (auxCube m z) w G →
      MemLp w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) →
        fracSeminorm (auxCube m z) α r w ≤
          ENNReal.ofReal C *
            ∑' k : {k : ℤ // m ≤ k},
              ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
                eLpNorm (fun x => euclidNorm (auxAverage m k.1 z G x))
                  (ENNReal.ofReal r) (volume.restrict (auxCube m z)) := by
  obtain ⟨C, hC, hrec⟩ := hreconstruction hα0 hα1 hr
  refine ⟨C, hC, ?_⟩
  intro m z a ha w G hw hwLp
  have hW := Weighted.memH1a_memW11 (auxCube_isOpenBoundedConvexDomain m z)
    (auxCube_nonempty m z) ha hw
  exact hrec m z w G hW.2.2.1 hW.1 (Integrable.of_eval hW.2.1) hwLp


end CoarseDeGiorgi.LowerFractional
