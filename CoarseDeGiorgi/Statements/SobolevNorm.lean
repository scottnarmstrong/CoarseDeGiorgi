import CoarseDeGiorgi.Statements.IsWeakDerivArray
import CoarseDeGiorgi.Statements.ArrayFracSeminorm
import Homogenization.Ambient.CoefficientField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

/-- The Sobolev norm `‖w‖_{W^{β,ξ}(U)}`: for an open `U`, an order `β ≥ 0`, written `β = m + α` with `m = ⌊β⌋₊` and
`0 ≤ α = β - m < 1`, and `1 ≤ ξ < ∞`,
`‖w‖_{W^{β,ξ}(U)} = (∑_{j=0}^m ‖∇ʲw‖_{L^ξ(U)}^ξ + [∇ᵐw]_{W^{α,ξ}(U)}^ξ)^{1/ξ}`,
the seminorm omitted if `α = 0`. Here `∇ʲw` is the array of the weak partial derivatives of
order `j` (`IsWeakDerivArray`; `j = 0` is `w` itself), `‖∇ʲw‖_{L^ξ(U)}` is the `L^ξ(U)` norm of
its pointwise Euclidean norm `|∇ʲw(x)| = (∑_ι (∂^ι w(x))²)^{1/2}`, and the seminorm is
`arrayFracSeminorm` (e.fractional.seminorm with the Euclidean array norm).

The infimum runs over all families `D j` (`j ≤ m`) of weak derivative arrays of `w` on `U`.
On an open `U` these are unique a.e. (`isWeakDerivArray_ae_eq`), so the infimum is the value at
the arrays `∇ʲw` (`sobolevNorm_eq_of_isWeakDerivArray`); it is `⊤` (the infimum of the empty family) when `w`
has no weak derivative arrays up to order `m`. For `0 < β < 1` this is the
`fracNorm` expression, and `W^{0,ξ}(U) = L^ξ(U)`. Norms may be infinite. -/
noncomputable def sobolevNorm {d : ℕ} (U : Set (Vec d)) (_hU : IsOpen U) (β ξ : ℝ) (_hβ : 0 ≤ β)
    (_hξ : 1 ≤ ξ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  ⨅ (D : (j : Fin (⌊β⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ)
    (_ : ∀ j : Fin (⌊β⌋₊ + 1), IsWeakDerivArray U j w (D j)),
    ((∑ j : Fin (⌊β⌋₊ + 1),
        ENNReal.rpow
          (eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal ξ)
            (volume.restrict U)) ξ) +
      (if β - ⌊β⌋₊ = 0 then 0
        else ENNReal.rpow (arrayFracSeminorm U (β - ⌊β⌋₊) ξ (D (Fin.last ⌊β⌋₊))) ξ)).rpow
      (1 / ξ)

end CoarseDeGiorgi
