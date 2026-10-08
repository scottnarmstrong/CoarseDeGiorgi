module

public import CoarseDeGiorgi.Selection.SourceRepresentatives
public import CoarseDeGiorgi.Assembly.HybridFractional
public import CoarseDeGiorgi.Weighted.Truncation.PositivePart
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

namespace CoarseDeGiorgi.Selection
open Homogenization MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section


theorem source_truncation_pair {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemH1a a (originCube 1) u G) (level : ℝ) :
    MemH1a a (originCube 1) (fun x => max (u x - level) 0)
      (positiveTruncationGradient u G level) := by
  have hunit := Assembly.hybrid_unitCube_domain (d := d)
  have hh := Weighted.MemH1a.max_sub_const hunit.1 hunit.2 ha hu level
  have heq : {x | level < u x}.indicator G = positiveTruncationGradient u G level := by
    funext x
    simp only [indicator_apply, mem_ofPred_eq, positiveTruncationGradient]
  rwa [heq] at hh

end
end CoarseDeGiorgi.Selection
