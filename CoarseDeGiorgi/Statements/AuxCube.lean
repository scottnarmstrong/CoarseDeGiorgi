module

public import Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def auxCube {d : ℕ} (m : ℤ) (z : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - (z i : ℝ) * (3 : ℝ) ^ (-m)| <
    ((3 : ℝ) ^ (1 - m)) / 2}

end

end CoarseDeGiorgi
