import CoarseDeGiorgi.Statements.PositivePart

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def positiveCap {d : ℕ} (v : Vec d → ℝ)
    (c : ℝ) (N : ℝ≥0∞) : Vec d → ℝ :=
  fun x => if N = ⊤ then positivePart (fun y => v y - c) x
    else min (positivePart (fun y => v y - c) x) N.toReal

end CoarseDeGiorgi
