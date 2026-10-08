module

public import CoarseDeGiorgi.Statements.ExteriorCell
public import CoarseDeGiorgi.Statements.ClosedTriadicCube
public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.InfSupDist

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- `𝒲_h`, the Whitney simplices whose selected cube `D` satisfies
`dist_∞(D̄, τ□̄₀) < h`. -/
def whitneySimplicesNear {d : ℕ} (τ h : ℝ) : Set (ExteriorCell d τ) :=
  {cell | infSupDist (closedTriadicCube cell.1.val) (closedReferenceCube (d := d) τ) < h}

end CoarseDeGiorgi
