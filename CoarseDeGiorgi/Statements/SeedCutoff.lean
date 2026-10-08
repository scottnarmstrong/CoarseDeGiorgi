import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def seedCutoff (u : ℝ) : ℝ := min 1 (max 0 (2 - 2 * u))

end CoarseDeGiorgi
