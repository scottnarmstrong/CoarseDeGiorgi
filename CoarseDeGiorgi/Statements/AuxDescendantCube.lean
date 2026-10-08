module

public import Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def auxDescendantCube {d : ℕ} (m k : ℤ) (z n : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - ((z i : ℝ) * (3 : ℝ) ^ (-m) +
      (n i : ℝ) * (3 : ℝ) ^ (1 - k))| < ((3 : ℝ) ^ (1 - k)) / 2}

end

end CoarseDeGiorgi
