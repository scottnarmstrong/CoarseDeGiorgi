module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.WeightedEnergy

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def h1aWeightedNorm {d : ℕ} (a : CoeffField d) (Q : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) : ℝ≥0∞ :=
  (ENNReal.ofReal ((volumeAverage Q w) ^ 2) + weightedEnergy a Q G).rpow (1 / 2)

end CoarseDeGiorgi
