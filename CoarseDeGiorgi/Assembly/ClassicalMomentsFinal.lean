import CoarseDeGiorgi.Assembly.ClassicalMomentsLower
import CoarseDeGiorgi.Statements.Csub
import CoarseDeGiorgi.Statements.LocallyBoundedAbove
import CoarseDeGiorgi.Weighted.LowerSpecNorm

/-! Corollary C with its lower-response input discharged by the proved norm
bound. The helper below takes the joint Theorem A statement explicitly. -/

namespace CoarseDeGiorgi.Assembly.ClassicalMomentsImpl

open Homogenization MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

/-- The two choices of `lowerResponseInv` come from the same existence and uniqueness theorem. -/
lemma corollary_lowerResponseInv_eq_spec {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    lowerResponseInv a V hV hne ha = Weighted.LowerResponseImpl.lowerResponseInv a V hV hne ha := rfl

/-- The lower norm bound holds in every dimension. -/
theorem corollary_lower_norm_bound {d : ℕ} (a : CoeffField d) : LowerNormBound a := by
  intro V hV hne ha
  rw [corollary_lowerResponseInv_eq_spec]
  exact Weighted.LowerResponseImpl.lowerResponseInv_norm_le hV hne ha

end CoarseDeGiorgi.Assembly.ClassicalMomentsImpl
