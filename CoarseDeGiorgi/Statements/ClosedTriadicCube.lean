module

public import CoarseDeGiorgi.Statements.TriadicCenter
public import Homogenization.Ambient.CoefficientField
public import Homogenization.Multiscale.CubeAverage

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def closedTriadicCube {d : ℕ} (D : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i, |x i - triadicCenter D i| ≤ cubeScaleFactor D / 2}

end

end CoarseDeGiorgi
