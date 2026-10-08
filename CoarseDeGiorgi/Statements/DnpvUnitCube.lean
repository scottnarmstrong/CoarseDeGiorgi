module

public import Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def dnpvUnitCube (n : ℕ) : Set (Vec n) :=
  {x | ∀ i, (-1 / 2 : ℝ) < x i ∧ x i < (1 / 2 : ℝ)}

end

end CoarseDeGiorgi
