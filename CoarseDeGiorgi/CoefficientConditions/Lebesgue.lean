import CoarseDeGiorgi.Assembly.ClassicalMomentsFinal

/-! Theorem D(i): Lebesgue moment bounds for all `s, t > 0` (no range or `θ` condition),
assembled from the series and lower-norm lemmas of the Corollary C development. -/

open Homogenization MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.CoefficientConditions

theorem moment_bounds_lebesgue_aux {d : ℕ} {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hs : 0 < s) (ht : 0 < t) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hap : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) < ⊤)
    (haq : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
      (volume.restrict (originCube 1)) < ⊤) :
    upperMoment a ha s p hs hp.le ≤
        eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) ∧
      (lowerMoment a ha t q ht hq.le)⁻¹ ≤
        eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) (volume.restrict (originCube 1)) ∧
      contrast a ha s t p q hs ht hp.le hq.le ≤
        eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) *
          eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) (volume.restrict (originCube 1)) := by
  have hl : Assembly.ClassicalMomentsImpl.LowerNormBound a :=
    Assembly.ClassicalMomentsImpl.corollary_lower_norm_bound a
  exact ⟨Assembly.ClassicalMomentsImpl.upperMoment_le_classical a ha hp.le hs hap,
    Assembly.ClassicalMomentsImpl.lowerMoment_inv_le_classical_of_lower_norm a ha hl hq.le ht haq,
    Assembly.ClassicalMomentsImpl.contrast_le_classical_of_lower_norm a ha hl hp.le hq.le hs ht hap haq⟩

end CoarseDeGiorgi.CoefficientConditions
