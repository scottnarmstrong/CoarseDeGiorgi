module

public import CoarseDeGiorgi.Statements.SobolevNorm

public import CoarseDeGiorgi.NegSobolev.SobolevNormFacts

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

/-- The characterization of `sobolevNorm`: on an open `U`, the norm is the source formula
`(∑_{j=0}^m ‖∇ʲw‖_{L^ξ(U)}^ξ + [∇ᵐw]_{W^{α,ξ}(U)}^ξ)^{1/ξ}` evaluated at any family of weak
derivative arrays of `w`. -/
theorem sobolevNorm_eq_of_isWeakDerivArray {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {β ξ : ℝ} (hβ : 0 ≤ β) (hξ : 1 ≤ ξ) {w : Vec d → ℝ}
    (D : (j : Fin (⌊β⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ)
    (hD : ∀ j : Fin (⌊β⌋₊ + 1), IsWeakDerivArray U j w (D j)) :
    sobolevNorm U hU β ξ hβ hξ w =
      ((∑ j : Fin (⌊β⌋₊ + 1),
          ENNReal.rpow (eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal ξ)
            (volume.restrict U)) ξ) +
        (if β - ⌊β⌋₊ = 0 then 0
          else ENNReal.rpow (arrayFracSeminorm U (β - ⌊β⌋₊) ξ (D (Fin.last ⌊β⌋₊))) ξ)).rpow (1 / ξ)
:=
  by exact CoarseDeGiorgi.NegSobolev.sobolevNorm_eq_of_isWeakDerivArray hU hβ hξ D hD

end CoarseDeGiorgi
