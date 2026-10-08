module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

/-- `D` is the array `∇ʲw` of the weak partial derivatives of order `j` of `w`
on `U`. The entry `D ι`, `ι : Fin j → Fin d`, is the weak derivative `∂_{ι 0} ⋯ ∂_{ι (j-1)} w`
(all `d ^ j` ordered index tuples). The function `w` and every entry are locally integrable on `U`,
and for every `φ ∈ C_c^∞(U)` (smooth, compact support, `tsupport φ ⊆ U`, as in
`IsWeightedSubsolution`), `∫_U w ∂^ι φ = (-1)^j ∫_U (D ι) φ`, where
`∂^ι φ (x) = iteratedFDeriv ℝ j φ x (e_{ι 0}, …, e_{ι (j-1)})`. For `j = 0` the identity reads
`∫_U w φ = ∫_U (D ι) φ`, so `D` is the one-entry array `w` (a.e.). On an open `U` such arrays are
unique a.e. The source uses weak derivatives on open sets; for any `U` the predicate is this
identity against test functions supported in `U`. -/
def IsWeakDerivArray {d : ℕ} (U : Set (Vec d)) (j : ℕ) (w : Vec d → ℝ)
    (D : (Fin j → Fin d) → Vec d → ℝ) : Prop :=
  LocallyIntegrableOn w U volume ∧
    ∀ ι : Fin j → Fin d,
      LocallyIntegrableOn (D ι) U volume ∧
        ∀ φ : Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ →
          tsupport φ ⊆ U →
          ∫ x in U, w x * iteratedFDeriv ℝ j φ x (fun k => basisVec (ι k)) ∂volume =
            (-1 : ℝ) ^ j * ∫ x in U, D ι x * φ x ∂volume

end CoarseDeGiorgi
