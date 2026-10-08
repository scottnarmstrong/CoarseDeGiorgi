module

public import CoarseDeGiorgi.Whitney.Harmonic.Sampling
public import CoarseDeGiorgi.Whitney.Harmonic.Cellwise
public import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.UpperResponseSpec
public import CoarseDeGiorgi.Weighted.LowerSpecNorm
public import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import CoarseDeGiorgi.Statements.SimplexCellNonempty
public import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell

/-! The energy identity `e.harmonic.energy` on a Whitney simplex. -/

@[expose] public section

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
