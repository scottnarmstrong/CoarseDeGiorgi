module

public import CoarseDeGiorgi.Weighted.Truncation.PositivePart
public import CoarseDeGiorgi.Weighted.PairOperations

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Addition of a constant preserves membership and the gradient. -/
theorem MemH1a.add_const (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) (c : ℝ) :
    CoarseDeGiorgi.MemH1a a V (fun x => u x + c) G := by
  simpa [Function.comp_def] using
    MemH1a.comp hV hne ha hu (Φ := fun t : ℝ => t + c)
      (contDiff_id.add contDiff_const) (L := 1) (by intro t; simp)



end CoarseDeGiorgi.Weighted
