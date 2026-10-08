module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.EuclidNorm
public import CoarseDeGiorgi.Statements.RStarParam

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessFinal

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem weak_harnack_sharpness (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ (a : ℝ → ℝ) (ha : IsWeightedCoeffOn (originCube 1)
        (fun x : Vec d => a (euclidNorm x) • (1 : Mat d))),
      upperMoment (fun x : Vec d => a (euclidNorm x) • (1 : Mat d)) ha s p hs hp.le < ⊤ ∧
      0 < lowerMoment (fun x : Vec d => a (euclidNorm x) • (1 : Mat d)) ha t q ht hq.le ∧
      ∃ (u : ℝ → Vec d → ℝ) (G : ℝ → Vec d → Vec d),
        (∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u ε x) ∧
          IsWeightedSupersolution (fun x : Vec d => a (euclidNorm x) • (1 : Mat d))
            (originCube 1) (u ε) (G ε)) ∧
        (∃ m : ℝ≥0∞, 0 < m ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
          nonnegativeEssInf (originCube (1 / 2)) (u ε) = m) ∧
        ∀ (η : ℝ) (hη : 0 < η), rStarParam (d := d) q t / 2 < η →
          Tendsto (fun ε : ℝ =>
            normalizedLpMoment η hη (originCube (5 / 8)) (u ε) /
              nonnegativeEssInf (originCube (1 / 2)) (u ε))
            (𝓝[>] 0) (𝓝 ⊤)
:=
  by exact CoarseDeGiorgi.SharpnessExamples.weakHarnackSharpness_proved d _hd p q s t hp hq hs ht _hθ

end CoarseDeGiorgi
