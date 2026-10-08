module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Harnack.Solutions.Harnack

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Harnack.Final

/-- Apply the weak-Harnack statement supplied as `hWeak` to derive the
exact Harnack conclusion (`t.harnack`). -/
theorem harnack_proved
    (hWeak : ∀ (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
      (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
      (_hθ : 0 < paramTheta d p q s t),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            normalizedLpMoment (harnackEtaParam q) (by
                have _hq0 : 0 < q := lt_trans (by norm_num) hq
                dsimp [harnackEtaParam, paramR]
                positivity)
              (originCube (5 / 8)) u ≤
              ENNReal.ofReal (Real.exp
                (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
                nonnegativeEssInf (originCube (1 / 2)) u) :
    ∀ (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
      (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
      (_hθ : 0 < paramTheta d p q s t),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSolution a (originCube 1) u G →
            eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
              ENNReal.ofReal (Real.exp
                (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
                nonnegativeEssInf (originCube (1 / 2)) u := by
  intro d hd p q s t hp hq hs ht hθ
  exact Solutions.harnack_of_weak_harnack_root hd p q s t hp hq hs ht hθ
    (hWeak d hd p q s t hp hq hs ht hθ)

end CoarseDeGiorgi.Harnack.Final
