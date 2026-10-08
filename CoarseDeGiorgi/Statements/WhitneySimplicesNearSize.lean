module

public import CoarseDeGiorgi.Statements.WhitneySimplicesNear

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- `𝒲_h^j`, the simplices of `𝒲_h` of size `3^{-j}`, i.e. whose selected cube has
side length `3^{1-j}` (`e.whitney.simplex.size`). -/
def whitneySimplicesNearSize {d : ℕ} (τ h : ℝ) (j : ℕ) : Set (ExteriorCell d τ) :=
  {cell | cell ∈ whitneySimplicesNear τ h ∧ cell.1.val.scale = 1 - (j : ℤ)}

end CoarseDeGiorgi
