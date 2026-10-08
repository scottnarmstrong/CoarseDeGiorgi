module

public import CoarseDeGiorgi.Statements.OriginCube
public import Mathlib.MeasureTheory.Function.EssSup

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The essential infimum of the nonnegative lift of u, under volume restricted to V.
It agrees with essinf u when u is nonnegative a.e.; arbitrary V uses ENNReal
lattice conventions, including value ⊤ for the zero measure. -/
noncomputable def nonnegativeEssInf {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)

end CoarseDeGiorgi
