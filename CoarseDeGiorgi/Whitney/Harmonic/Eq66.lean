import CoarseDeGiorgi.Whitney.Harmonic.Sampling
import CoarseDeGiorgi.Whitney.Harmonic.Cellwise
import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
import CoarseDeGiorgi.Statements.UpperResponseOnCell
import CoarseDeGiorgi.Statements.UpperResponseSpec
import CoarseDeGiorgi.Weighted.LowerSpecNorm
import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
import CoarseDeGiorgi.Statements.SimplexCellNonempty
import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell

/-! The energy identity `e.harmonic.energy` on a Whitney simplex. -/

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Matrix.Norms.L2Operator
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

theorem upperResponse_congr {a : CoeffField d} {V W : Set (Vec d)} (h : V = W)
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    (hW : IsOpenBoundedConvexDomain W) (hneW : W.Nonempty) (haW : IsWeightedCoeffOn W a) :
    CoarseDeGiorgi.upperResponse a V hV hne ha = CoarseDeGiorgi.upperResponse a W hW hneW haW := by
  subst h; rfl

end CoarseDeGiorgi.Whitney.Harmonic
