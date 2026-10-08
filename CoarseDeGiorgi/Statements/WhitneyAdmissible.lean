import CoarseDeGiorgi.Statements.ClosedReferenceCube
import CoarseDeGiorgi.Statements.FivefoldClosedTriadicCube
import Homogenization.Multiscale.CubeAverage

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def whitneyAdmissible {d : ℕ} (τ : ℝ) (D : TriadicCube d) : Prop :=
  Disjoint (fivefoldClosedTriadicCube D) (closedReferenceCube τ)

end

end CoarseDeGiorgi
