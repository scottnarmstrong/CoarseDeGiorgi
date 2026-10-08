module

public import CoarseDeGiorgi.LowerFractional.Aliases
public import CoarseDeGiorgi.LowerFractional.Restriction
public import CoarseDeGiorgi.Weighted.LowerResponse
public import CoarseDeGiorgi.Weighted.LowerSpecNorm

/-! The mean-gradient bounds `e.lower.mean.gradient` for the lower response.
Proof irrelevance identifies the choice definition's proof inputs. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator



/-- Exact squared Euclidean-length consequence, with the scoped operator norm. -/
theorem lower_mean_gradient_norm {d : ℕ} {a : CoeffField d} {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) :
    vecNormSq (volumeAverageVec V G) ≤
      ‖Aliases.lowerResponseInv a V hV hne ha‖ *
        volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x))) :=
  Weighted.LowerResponseImpl.lowerResponseInv_mean_gradient_norm hV hne ha hw



end CoarseDeGiorgi.LowerFractional
