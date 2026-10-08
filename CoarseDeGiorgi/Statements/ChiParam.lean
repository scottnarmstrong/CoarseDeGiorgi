import CoarseDeGiorgi.Statements.RStarParam

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def chiParam (d : ℕ) (q t : ℝ) : ℝ :=
  @rStarParam d q t / paramR q

end CoarseDeGiorgi
