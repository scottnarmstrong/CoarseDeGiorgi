import CoarseDeGiorgi.Statements.Contrast

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def crossoverExponent {d : ℕ} (c : ℝ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s t p q : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q) : ℝ :=
  c * ((1 + contrast a ha s t p q hs ht hp hq).rpow (-(1 / 2 : ℝ))).toReal

end CoarseDeGiorgi
