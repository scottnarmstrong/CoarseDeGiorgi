import CoarseDeGiorgi.Statements.LocalBoundedness
import CoarseDeGiorgi.Statements.PositivePart

/-! # Lower bound on the contrast from Theorem A

End of Step 3 of the proof of Proposition `p.sharpness.polynomial`: Theorem A with
`ρ₁ = 1/2`, `ρ₂ = 3/4` and `η = 2` applied to the positive part of the solution, whose height is
at least one, against its `L²` norm. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

/-- The inequality `1 ≤ K Θ^{(d-1)/(4θ)} ‖u₊‖_{L²(¾□₀)}` from Theorem A, with `K` depending
only on `d, p, q, s, t`. -/
theorem optimalPowers_theoremA_inequality (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
        (u : Vec d → ℝ) (G : Vec d → Vec d),
        upperMoment a ha s p hs hp.le < ⊤ → 0 < lowerMoment a ha t q ht hq.le →
        IsWeightedSubsolution a (originCube 1) (positivePart u) G →
        1 ≤ eLpNorm (positivePart u) ⊤ (volume.restrict (originCube (1 / 2))) →
        1 ≤ ENNReal.ofReal K *
          (contrast a ha s t p q hs ht hp.le hq.le).rpow
            ((d - 1 : ℝ) / (4 * paramTheta d p q s t)) *
          eLpNorm (positivePart u) (ENNReal.ofReal 2) (volume.restrict (originCube (3 / 4))) := by
  obtain ⟨γ, hγ, ⟨C_A, hCA, hA⟩, _⟩ := CoarseDeGiorgi.local_boundedness d hd p q s t hp hq hs ht hθ
  refine ⟨(C_A + 1) * (1 / 4 : ℝ) ^ (-γ), by positivity, ?_⟩
  intro a ha u G hU hL hsub hhi
  obtain ⟨_, h⟩ := hA a ha hU hL (positivePart u) G hsub
  have hpp : positivePart (positivePart u) = positivePart u := by
    funext x; simp [positivePart]
  have h1 := (h (1 / 2) (3 / 4) (by norm_num) (by norm_num) (by norm_num)).1
  rw [hpp] at h1
  have hR : ENNReal.ofReal (3 / 4 - 1 / 2) = ENNReal.ofReal (1 / 4) := by norm_num
  rw [hR] at h1
  have h2 : ENNReal.ofReal C_A * (ENNReal.ofReal (1 / 4)).rpow (-γ) ≤
      ENNReal.ofReal ((C_A + 1) * (1 / 4 : ℝ) ^ (-γ)) := by
    rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos (by norm_num),
      ← ENNReal.ofReal_mul hCA]
    exact ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ (1 / 4 : ℝ) ^ (-γ) := by positivity
      nlinarith)
  have h3 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h3] at h1
  calc (1 : ℝ≥0∞) ≤ _ := hhi
    _ ≤ _ := h1
    _ ≤ _ := by
      gcongr
/-- Solving `1 ≤ K Θ^e B y` for `Θ`. -/
theorem optimalPowers_solve_for_contrast {T : ℝ≥0∞} (hT : T ≠ ⊤) {K B y e : ℝ}
    (hK : 0 < K) (hB : 0 < B) (hy : 0 < y) (he : 0 < e)
    (h : 1 ≤ ENNReal.ofReal K * T.rpow e * ENNReal.ofReal (B * y)) :
    ENNReal.ofReal (((K * B) * y)⁻¹ ^ (1 / e)) ≤ T := by
  set Tr := T.toReal with hTr
  have hT' : T = ENNReal.ofReal Tr := (ENNReal.ofReal_toReal hT).symm
  have hTr0 : 0 ≤ Tr := ENNReal.toReal_nonneg
  rw [hT', ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_nonneg hTr0 he.le,
    ← ENNReal.ofReal_mul hK.le, ← ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hTr0 _))] at h
  have h1 : 1 ≤ K * Tr ^ e * (B * y) := ENNReal.one_le_ofReal.1 h
  have h2 : ((K * B) * y)⁻¹ ≤ Tr ^ e := by
    rw [inv_le_iff_one_le_mul₀' (by positivity)]
    have : K * Tr ^ e * (B * y) = (K * B * y) * Tr ^ e := by ring
    linarith
  have h3 : ((K * B) * y)⁻¹ ^ (1 / e) ≤ (Tr ^ e) ^ (1 / e) :=
    Real.rpow_le_rpow (by positivity) h2 (by positivity)
  rw [← Real.rpow_mul hTr0, mul_one_div_cancel he.ne', Real.rpow_one] at h3
  rw [hT']
  exact ENNReal.ofReal_le_ofReal h3

end CoarseDeGiorgi.SharpnessExamples
