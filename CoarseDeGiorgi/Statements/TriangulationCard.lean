import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.Triangulation
import CoarseDeGiorgi.Moments.Cells

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem triangulation_card {d : ℕ} (k : ℕ) :
    (triangulation (d := d) k).card = Nat.factorial d * 3 ^ (k * d) :=
  CoarseDeGiorgi.Moments.triangulation_card k

end CoarseDeGiorgi
