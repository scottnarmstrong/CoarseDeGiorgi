import CoarseDeGiorgi.Statements.CubeFaceMeasure
import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def surfaceMeasure {d : ℕ} (τ : ℝ) : Measure (Vec d) := by
  classical
  exact ∑ i : Fin d, ∑ positive : Bool, cubeFaceMeasure τ i positive

end

end CoarseDeGiorgi
