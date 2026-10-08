import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def cubeSurface {d : ℕ} (τ : ℝ) : Set (Vec d) :=
  {x | ‖x‖ = τ / 2}

end

end CoarseDeGiorgi
