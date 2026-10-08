import CoarseDeGiorgi.Statements.TriadicCenter
import Homogenization.Ambient.CoefficientField
import Homogenization.Multiscale.CubeAverage

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def closedTriadicCube {d : ℕ} (D : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i, |x i - triadicCenter D i| ≤ cubeScaleFactor D / 2}

end

end CoarseDeGiorgi
