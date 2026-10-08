import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.WeightedEnergy

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def h1aWeightedNorm {d : ℕ} (a : CoeffField d) (Q : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) : ℝ≥0∞ :=
  (ENNReal.ofReal ((volumeAverage Q w) ^ 2) + weightedEnergy a Q G).rpow (1 / 2)

end CoarseDeGiorgi
