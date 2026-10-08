import CoarseDeGiorgi.Statements.EuclideanSetDistance
import CoarseDeGiorgi.Statements.UpperResponseOnCell
import CoarseDeGiorgi.Statements.CubeSurface

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def sampledUpperResponse {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (τ : ℝ) : ℝ≥0∞ :=
  ⨆ η : SimplexIndex d k,
    ⨆ (_hnear : euclideanSetDistance (closure (simplexCell k η)) (cubeSurface τ) ≤
        ENNReal.ofReal (100 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℤ)))),
      ENNReal.ofReal ‖upperResponseOnCell k a ha η‖

end CoarseDeGiorgi
