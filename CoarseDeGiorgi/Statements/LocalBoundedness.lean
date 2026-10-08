import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PositivePart
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.LocallyBoundedAbove

import CoarseDeGiorgi.Statements.CaccioppoliInequality
import CoarseDeGiorgi.Statements.EnergyToSupremum
import CoarseDeGiorgi.TheoremA.LocalBoundedness
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem local_boundedness (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ γ : ℝ, 0 < γ ∧
      ((∃ C_A : ℝ, 0 ≤ C_A ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          LocallyBoundedAbove (originCube 1) u ∧
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_A *
            (ENNReal.ofReal (R - ρ)).rpow (-γ) *
            (contrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (4 * paramTheta d p q s t)) *
            eLpNorm (positivePart u) 2 (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) 2
              (volume.restrict (originCube R)) < ⊤)) ∧
      (∀ η : ℝ, 0 < η → η < 2 →
        ∃ C_η : ℝ, 0 ≤ C_η ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_η *
            (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)) *
            (contrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (2 * η * paramTheta d p q s t)) *
            eLpNorm (positivePart u) (ENNReal.ofReal η) (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) (ENNReal.ofReal η)
              (volume.restrict (originCube R)) < ⊤)))
:=
  TheoremA.local_boundedness_of_props CoarseDeGiorgi.caccioppoli_inequality CoarseDeGiorgi.energy_to_supremum d _hd p q s t hp hq hs ht _hθ

end CoarseDeGiorgi
