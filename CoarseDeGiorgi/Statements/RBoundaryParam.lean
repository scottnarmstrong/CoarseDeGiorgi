import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.ParamR

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def rBoundaryParam {d : ℕ} (q t : ℝ) : ℝ :=
  let r := paramR q
  (((d : ℝ) - 1) * r) / (((d : ℝ) - 1) - alphaParam t * r)

end CoarseDeGiorgi
