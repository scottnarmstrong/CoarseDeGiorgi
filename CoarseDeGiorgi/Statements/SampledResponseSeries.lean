import CoarseDeGiorgi.Statements.SampledUpperResponse

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def sampledResponseSeries {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s p τ : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ,
    ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * (s + ((d : ℝ) - 1) / (2 * p))))) *
      (sampledUpperResponse a ha k τ).rpow (1 / 2 : ℝ)

end CoarseDeGiorgi
