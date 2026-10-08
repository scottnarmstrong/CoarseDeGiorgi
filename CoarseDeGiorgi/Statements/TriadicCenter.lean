module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Multiscale.CubeAverage

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def triadicCenter {d : ℕ} (D : TriadicCube d) : Vec d :=
  fun i => (D.index i : ℝ) * cubeScaleFactor D

end

end CoarseDeGiorgi
