import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def positiveTruncationGradient {d : ℕ} (u : Vec d → ℝ)
    (G : Vec d → Vec d) (level : ℝ) : Vec d → Vec d :=
  fun x => if level < u x then G x else 0

end CoarseDeGiorgi
