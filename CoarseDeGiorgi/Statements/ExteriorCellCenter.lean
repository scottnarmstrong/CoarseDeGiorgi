module

public import CoarseDeGiorgi.Statements.ExteriorCell
public import CoarseDeGiorgi.Statements.TriadicCenter

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def exteriorCellCenter {d : ℕ} {τ : ℝ} (cell : ExteriorCell d τ) :
    Vec d :=
  fun i => triadicCenter cell.1.val i +
    (3 : ℝ) ^ (cell.1.val.scale - 1) * ((cell.2.1 i).val - 1 : ℝ)

end CoarseDeGiorgi
