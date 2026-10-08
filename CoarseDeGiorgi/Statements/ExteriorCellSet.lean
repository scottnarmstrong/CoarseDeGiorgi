import CoarseDeGiorgi.Statements.ExteriorCellCenter
import CoarseDeGiorgi.Statements.Simplex

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def exteriorCellSet {d : ℕ} {τ : ℝ} (cell : ExteriorCell d τ) :
    Set (Vec d) :=
  simplex (cell.1.val.scale - 1) cell.2.2 (exteriorCellCenter cell)

end CoarseDeGiorgi
