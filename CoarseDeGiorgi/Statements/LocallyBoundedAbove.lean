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

def LocallyBoundedAbove {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∀ K : Set (Vec d), IsCompact K → K ⊆ V →
    ∃ M : ℝ, ∀ᵐ x ∂(volume.restrict K), u x ≤ M

end CoarseDeGiorgi
