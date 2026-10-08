import CoarseDeGiorgi.Statements.ExteriorCell
import CoarseDeGiorgi.Statements.ClosedTriadicCube
import CoarseDeGiorgi.Statements.ClosedReferenceCube
import CoarseDeGiorgi.Statements.InfSupDist

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- `𝒲_h`, the Whitney simplices whose selected cube `D` satisfies
`dist_∞(D̄, τ□̄₀) < h`. -/
def whitneySimplicesNear {d : ℕ} (τ h : ℝ) : Set (ExteriorCell d τ) :=
  {cell | infSupDist (closedTriadicCube cell.1.val) (closedReferenceCube (d := d) τ) < h}

end CoarseDeGiorgi
