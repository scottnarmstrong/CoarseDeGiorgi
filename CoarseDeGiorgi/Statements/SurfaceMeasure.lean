module

public import CoarseDeGiorgi.Statements.CubeFaceMeasure
public import Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def surfaceMeasure {d : ℕ} (τ : ℝ) : Measure (Vec d) := by
  classical
  exact ∑ i : Fin d, ∑ positive : Bool, cubeFaceMeasure τ i positive

end

end CoarseDeGiorgi
