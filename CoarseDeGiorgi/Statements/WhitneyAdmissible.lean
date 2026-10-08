module

public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.FivefoldClosedTriadicCube
public import Homogenization.Multiscale.CubeAverage

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def whitneyAdmissible {d : ℕ} (τ : ℝ) (D : TriadicCube d) : Prop :=
  Disjoint (fivefoldClosedTriadicCube D) (closedReferenceCube τ)

end

end CoarseDeGiorgi
