import CoarseDeGiorgi.Statements.TriadicCenter
import Homogenization.Ambient.CoefficientField
import Homogenization.Multiscale.CubeAverage

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def fivefoldClosedTriadicCube {d : ℕ} (D : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i, |x i - triadicCenter D i| ≤ (5 / 2 : ℝ) * cubeScaleFactor D}

end

end CoarseDeGiorgi
