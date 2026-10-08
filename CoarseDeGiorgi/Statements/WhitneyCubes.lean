import CoarseDeGiorgi.Statements.ClosedTriadicCube
import CoarseDeGiorgi.Statements.WhitneyAdmissible
import Homogenization.Multiscale.CubeAverage

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def whitneyCubes {d : ℕ} (τ : ℝ) : Set (TriadicCube d) :=
  {D | whitneyAdmissible τ D ∧
    ∀ E, whitneyAdmissible τ E → closedTriadicCube D ⊆ closedTriadicCube E → E = D}

end

end CoarseDeGiorgi
