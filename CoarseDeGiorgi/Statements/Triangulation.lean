import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.GridOffset

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def triangulation {d : ℕ} (k : ℕ) :
    Finset ((Fin d → ℤ) × Equiv.Perm (Fin d)) := by
  classical
  exact
    (Finset.univ : Finset ((Fin d → Fin (3 ^ k)) × Equiv.Perm (Fin d))).image
      (fun jp => (gridOffset k jp.1, jp.2))

end CoarseDeGiorgi
