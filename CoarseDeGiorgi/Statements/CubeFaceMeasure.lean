module

public import CoarseDeGiorgi.Statements.FaceCoordinateMeasures
public import Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def cubeFaceMeasure {d : ℕ} (τ : ℝ) (i : Fin d)
    (positive : Bool) : Measure (Vec d) :=
  Measure.pi (faceCoordinateMeasures τ i positive)

end

end CoarseDeGiorgi
