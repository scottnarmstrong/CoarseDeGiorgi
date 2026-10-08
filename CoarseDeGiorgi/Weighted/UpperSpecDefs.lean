module

public import CoarseDeGiorgi.Statements.UpperResponseExistsUnique
public import CoarseDeGiorgi.Weighted.ResponseBounds
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace CoarseDeGiorgi.Weighted.UpperResponseImpl

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The upper response matrix, selected from the response uniqueness statement. -/
noncomputable def upperResponse {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : Mat d :=
  Classical.choose (upperResponse_existsUnique hV hV₀ ha).exists

theorem upperResponse_posDef {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : (upperResponse a V hV hV₀ ha).PosDef :=
  (Classical.choose_spec (upperResponse_existsUnique hV hV₀ ha).exists).1

theorem upperResponse_directional {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    ((vecDot e (matVecMul (upperResponse a V hV hV₀ ha) e) : ℝ) : EReal) =
      upperDirectionalResponseSol a V e :=
  (Classical.choose_spec (upperResponse_existsUnique hV hV₀ ha).exists).2 e

theorem upperResponse_unique {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (M : Mat d) (hM : M.PosDef)
    (he : ∀ e : Vec d, ((vecDot e (matVecMul M e) : ℝ) : EReal) =
      upperDirectionalResponseSol a V e) : M = upperResponse a V hV hV₀ ha := by
  obtain ⟨A, _, hu⟩ := upperResponse_existsUnique hV hV₀ ha
  exact (hu M ⟨hM, he⟩).trans
    (hu _ ⟨upperResponse_posDef hV hV₀ ha, upperResponse_directional hV hV₀ ha⟩).symm

end CoarseDeGiorgi.Weighted.UpperResponseImpl
