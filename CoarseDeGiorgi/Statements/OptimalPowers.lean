import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PositivePart
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.IsWeightedSolution

import CoarseDeGiorgi.SharpnessExamples.OptimalPowersFinal
open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem optimal_powers (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ (a : ℝ → CoeffField d) (u : ℝ → Vec d → ℝ) (G : ℝ → Vec d → Vec d)
      (ha : ∀ ε, IsWeightedCoeffOn (originCube 1) (a ε)),
      -- each field is symmetric and uniformly elliptic, with constants depending on ε
      (∀ ε, 0 < ε → ε < 1 / 8 → ∃ lam Λ : ℝ, 0 < lam ∧
        ∀ᵐ x ∂(volume.restrict (originCube 1)), (a ε x).IsHermitian ∧
          ∀ ξ : Vec d, lam * vecDot ξ ξ ≤ vecDot ξ (matVecMul (a ε x) ξ) ∧
            vecDot ξ (matVecMul (a ε x) ξ) ≤ Λ * vecDot ξ ξ) ∧
      -- u_ε is a weighted solution for a_ε, and its positive part a weighted subsolution
      (∀ ε, 0 < ε → ε < 1 / 8 → IsWeightedSolution (a ε) (originCube 1) (u ε) (G ε) ∧
        ∃ G' : Vec d → Vec d,
          IsWeightedSubsolution (a ε) (originCube 1) (positivePart (u ε)) G') ∧
      -- uniformly integrable traces
      (∃ C : ℝ, ∀ ε, 0 < ε → ε < 1 / 8 →
        ∫ x in originCube 1, ((a ε x).trace + ((a ε x)⁻¹).trace) ≤ C) ∧
      -- the moments: Λ_ε ≍ ε^{-2θ}, λ_ε ≍ 1, Θ_ε ≍ ε^{-2θ}
      (∃ C : ℝ, 1 ≤ C ∧ ∀ ε, 0 < ε → ε < 1 / 8 →
        ENNReal.ofReal (C⁻¹ * ε ^ (-(2 * paramTheta d p q s t))) ≤
            upperMoment (a ε) (ha ε) s p hs hp.le ∧
          upperMoment (a ε) (ha ε) s p hs hp.le ≤
            ENNReal.ofReal (C * ε ^ (-(2 * paramTheta d p q s t))) ∧
          ENNReal.ofReal C⁻¹ ≤ lowerMoment (a ε) (ha ε) t q ht hq.le ∧
          lowerMoment (a ε) (ha ε) t q ht hq.le ≤ ENNReal.ofReal C ∧
          ENNReal.ofReal (C⁻¹ * ε ^ (-(2 * paramTheta d p q s t))) ≤
            contrast (a ε) (ha ε) s t p q hs ht hp.le hq.le ∧
          contrast (a ε) (ha ε) s t p q hs ht hp.le hq.le ≤
            ENNReal.ofReal (C * ε ^ (-(2 * paramTheta d p q s t)))) ∧
      -- the height of the positive part
      (∀ ε, 0 < ε → ε < 1 / 8 → ∀ ρ : ℝ, 1 / 2 ≤ ρ → ρ < 1 →
        eLpNorm (positivePart (u ε)) ⊤ (volume.restrict (originCube ρ)) =
          ENNReal.ofReal (1 + ρ ^ 2 / 4)) ∧
      -- the L^η norm of the positive part: ≍ ε^{(d-1)/η}, uniformly in ε and R
      (∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧ ∀ ε, 0 < ε → ε < 1 / 8 → ∀ R : ℝ, 1 / 2 < R → R ≤ 1 →
        ENNReal.ofReal (C⁻¹ * ε ^ (((d : ℝ) - 1) / η)) ≤
            eLpNorm (positivePart (u ε)) (ENNReal.ofReal η) (volume.restrict (originCube R)) ∧
          eLpNorm (positivePart (u ε)) (ENNReal.ofReal η) (volume.restrict (originCube R)) ≤
            ENNReal.ofReal (C * ε ^ (((d : ℝ) - 1) / η))) ∧
      -- consequently the ratio tends to ∞: the powers of Θ in Theorem A and Corollary B cannot be lowered
      (∀ ρ R η υ : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 → 0 < η → η ≤ 2 →
        υ < ((d : ℝ) - 1) / (2 * η * paramTheta d p q s t) →
        Tendsto (fun ε => eLpNorm (positivePart (u ε)) ⊤ (volume.restrict (originCube ρ)) /
            ((contrast (a ε) (ha ε) s t p q hs ht hp.le hq.le).rpow υ *
              eLpNorm (positivePart (u ε)) (ENNReal.ofReal η) (volume.restrict (originCube R))))
          (𝓝[>] 0) (𝓝 ⊤))
:=
  by
  exact CoarseDeGiorgi.SharpnessExamples.optimal_powers_proved d _hd p q s t hp hq hs ht _hθ

end CoarseDeGiorgi
