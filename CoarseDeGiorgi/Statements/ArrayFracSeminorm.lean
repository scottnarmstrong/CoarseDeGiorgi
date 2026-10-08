module

public import CoarseDeGiorgi.Statements.EuclidDist
public import Homogenization.Ambient.CoefficientField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

/-- The seminorm `e.fractional.seminorm` for an array-valued function `F = (F i)_{i : ι}`:
`[F]_{W^{α,r}(V)} = (∫_V ∫_V |F(x) - F(y)|^r / |x - y|^{d + α r} dx dy)^{1/r}`, where `|·|` on the
array `F(x) - F(y) ∈ ℝ^ι` is the Euclidean norm (as in the notation section: "On vectors, |·| is the Euclidean
norm") and `|x - y|` is `euclidDist`. It is `fracSeminorm` (via
`fracKernelWithDimension`) with `|w x - w y|` replaced by the Euclidean norm of the array
difference; for a one-entry array the two agree. Used with `F = ∇ᵐw` in `sobolevNorm`. -/
noncomputable def arrayFracSeminorm {d : ℕ} {ι : Type*} [Fintype ι] (V : Set (Vec d))
    (α r : ℝ) (F : ι → Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ p : Vec d × Vec d,
      ENNReal.ofReal
        (Real.sqrt (∑ i, (F i p.1 - F i p.2) ^ 2) ^ r /
          euclidDist p.1 p.2 ^ ((d : ℝ) + α * r))
    ∂((volume.restrict V).prod (volume.restrict V))).rpow (1 / r)

end CoarseDeGiorgi
