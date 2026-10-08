module

public import CoarseDeGiorgi.Statements.ParamR

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def harnackEtaParam (q : ℝ) : ℝ := paramR q / 4

end CoarseDeGiorgi
