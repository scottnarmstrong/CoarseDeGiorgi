import CoarseDeGiorgi.Statements.FaceCoordinateMeasures
import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Constructions.Pi

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def cubeFaceMeasure {d : ℕ} (τ : ℝ) (i : Fin d)
    (positive : Bool) : Measure (Vec d) :=
  Measure.pi (faceCoordinateMeasures τ i positive)

end

end CoarseDeGiorgi
