import CoarseDeGiorgi.Statements.ExteriorCellCenter

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def exteriorCellVertex {d : ℕ} {τ : ℝ} (cell : ExteriorCell d τ)
    (j : Fin (d + 1)) : Vec d :=
  fun i => exteriorCellCenter cell i + (3 : ℝ) ^ (cell.1.val.scale - 1) *
    (if (cell.2.2.symm i).val < j.val then -(1 / 2) else 1 / 2)

end CoarseDeGiorgi
