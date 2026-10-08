import CoarseDeGiorgi.Statements.LowerResponseExistsUnique
import CoarseDeGiorgi.Weighted.LowerResponse
import CoarseDeGiorgi.Weighted.ResponseBoundsLower
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace CoarseDeGiorgi.Weighted.LowerResponseImpl

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The inverse lower response matrix, selected from the response uniqueness statement. -/
noncomputable def lowerResponseInv {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : Mat d :=
  Classical.choose (lowerResponse_existsUnique hV hV₀ ha).exists

theorem lowerResponseInv_posDef {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : (lowerResponseInv a V hV hV₀ ha).PosDef :=
  (Classical.choose_spec (lowerResponse_existsUnique hV hV₀ ha).exists).1

theorem lowerResponseInv_directional {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    ((vecDot e (matVecMul (lowerResponseInv a V hV hV₀ ha) e) : ℝ) : EReal) =
      lowerDirectionalResponse a V e :=
  (Classical.choose_spec (lowerResponse_existsUnique hV hV₀ ha).exists).2 e

theorem lowerResponseInv_unique {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (M : Mat d) (hM : M.PosDef)
    (he : ∀ e : Vec d, ((vecDot e (matVecMul M e) : ℝ) : EReal) =
      lowerDirectionalResponse a V e) : M = lowerResponseInv a V hV hV₀ ha := by
  obtain ⟨A, _, hu⟩ := lowerResponse_existsUnique hV hV₀ ha
  exact (hu M ⟨hM, he⟩).trans
    (hu _ ⟨lowerResponseInv_posDef hV hV₀ ha, lowerResponseInv_directional hV hV₀ ha⟩).symm

end CoarseDeGiorgi.Weighted.LowerResponseImpl
