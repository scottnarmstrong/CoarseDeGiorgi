import CoarseDeGiorgi.Statements.WhitneyInterpolationDef

import CoarseDeGiorgi.Statements.WhitneyInterpolationExistsUnique
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The interpolant of Lemma `l.whitney.interpolation` is characterized by `IsWhitneyInterpolant`: it is one, and it is the only one. -/
theorem whitneyInterpolation_spec {d : ℕ} {τ : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) :
    IsWhitneyInterpolant τ vals (whitneyInterpolation hτ0 hτ1 vals) ∧
      ∀ g : Vec d → ℝ, IsWhitneyInterpolant τ vals g → g = whitneyInterpolation hτ0 hτ1 vals
:=
  ⟨Classical.choose_spec (CoarseDeGiorgi.whitney_interpolation_existsUnique hτ0 hτ1 vals).exists,
    fun _ hg => (CoarseDeGiorgi.whitney_interpolation_existsUnique hτ0 hτ1 vals).unique hg
      (Classical.choose_spec (CoarseDeGiorgi.whitney_interpolation_existsUnique hτ0 hτ1 vals).exists)⟩

end CoarseDeGiorgi
