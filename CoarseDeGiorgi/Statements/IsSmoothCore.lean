import CoarseDeGiorgi.Statements.SmoothGrad
import CoarseDeGiorgi.Statements.WeightedEnergy
import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    IntegrableOn φ V ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

end CoarseDeGiorgi
