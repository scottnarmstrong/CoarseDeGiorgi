import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def closedReferenceCube {d : ℕ} (τ : ℝ) : Set (Vec d) :=
  {x | ∀ i, |x i| ≤ τ / 2}

end

end CoarseDeGiorgi
