import CoarseDeGiorgi.SharpnessExamples.PolynomialField
import CoarseDeGiorgi.Sharpness.LineEquation.LineBasics

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem polynomialDiagonal_quadratic_bounds {d : ℕ} [NeZero d]
    {lam Λ : ℝ} {b : Fin d → ℝ}
    (hlo : ∀ i, lam ≤ b i) (hhi : ∀ i, b i ≤ Λ)
    (ξ : Vec d) :
    lam * vecDot ξ ξ ≤ vecDot ξ (matVecMul (Matrix.diagonal b) ξ) ∧
      vecDot ξ (matVecMul (Matrix.diagonal b) ξ) ≤ Λ * vecDot ξ ξ := by
  rw [Sharpness.vecDot_diagonal]
  have hnorm : vecDot ξ ξ = ∑ i, (ξ i) ^ 2 := by
    simp [vecDot, pow_two]
  rw [hnorm]
  constructor
  · calc
      lam * ∑ i, (ξ i) ^ 2 = ∑ i, lam * (ξ i) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, b i * (ξ i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlo i) (sq_nonneg _)
  · calc
      ∑ i, b i * (ξ i) ^ 2 ≤ ∑ i, Λ * (ξ i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hhi i) (sq_nonneg _)
      _ = Λ * ∑ i, (ξ i) ^ 2 := by rw [Finset.mul_sum]

/-- The polynomial cylinder has a.e. Hermitian matrix values and explicit
ellipticity constants on its parameter interval. -/
theorem polynomialCoefficientFamily_ellipticity {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {p q s t epsilon : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8) :
    ∃ lam Λ : ℝ, 0 < lam ∧
      ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)),
        (polynomialCoefficientFamily d q t epsilon x).IsHermitian ∧
          ∀ ξ : Vec d,
            lam * vecDot ξ ξ ≤
              vecDot ξ (matVecMul (polynomialCoefficientFamily d q t epsilon x) ξ) ∧
            vecDot ξ (matVecMul (polynomialCoefficientFamily d q t epsilon x) ξ) ≤
              Λ * vecDot ξ ξ := by
  have hTpos := polynomialHatT_pos (by omega : 2 ≤ d) hq ht
  have hTlt := polynomialHatT_lt_one hd hp hs hθ
  let lam := polynomialPerpendicular d q t epsilon
  let Λ := polynomialParallel d q t epsilon
  have hlam : 0 < lam := polynomialPerpendicular_pos hepsilon
  have hlam1 : lam ≤ 1 := by
    have hpow := Real.rpow_le_rpow hepsilon.le (by linarith : epsilon ≤ 1)
      (by linarith : 0 ≤ 2 * polynomialHatT d q t)
    dsimp [lam, polynomialPerpendicular]
    simpa only [Real.one_rpow] using hpow
  have hΛ1 : 1 ≤ Λ := by
    have hexp : 2 * polynomialHatT d q t - 2 ≤ 0 := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hepsilon (by linarith : epsilon ≤ 1) hexp
    have hpow' : 1 ≤ Real.rpow epsilon (2 * polynomialHatT d q t - 2) := by
      change 1 ≤ epsilon ^ (2 * polynomialHatT d q t - 2)
      simpa only [Real.one_rpow] using hpow
    have hfactor : 1 ≤ (d : ℝ) - 1 := by
      have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    dsimp [Λ, polynomialParallel]
    calc
      1 ≤ (d : ℝ) - 1 := hfactor
      _ ≤ ((d : ℝ) - 1) * Real.rpow epsilon (2 * polynomialHatT d q t - 2) := by
        calc
          _ = ((d : ℝ) - 1) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow' (by linarith)
  refine ⟨lam, Λ, hlam, ?_⟩
  filter_upwards with x
  have hfield : polynomialCoefficientFamily d q t epsilon x =
      cylinderCoefficient epsilon Λ lam x := by
    change (if 0 < epsilon ∧ epsilon < 1 / 8 then
      cylinderCoefficient epsilon (polynomialParallel d q t epsilon)
        (polynomialPerpendicular d q t epsilon) else fun _ => 1) x = _
    split_ifs with h
    · rfl
    · exact (h ⟨hepsilon, hepsilon8⟩).elim
  rw [hfield]
  by_cases hx : x ∈ responseCylinder epsilon
  · simp only [cylinderCoefficient, hx]
    have hdiag : (cylinderDiagonal (d := d) Λ lam).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      by_cases hij : i = j
      · subst j
        simp [cylinderDiagonal]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [cylinderDiagonal, hij, hji]
    refine ⟨hdiag, ?_⟩
    intro ξ
    apply polynomialDiagonal_quadratic_bounds
    · intro i
      by_cases hi : i.val = 0
      · simpa [hi] using hlam1.trans hΛ1
      · simp [hi]
    · intro i
      by_cases hi : i.val = 0
      · simp [hi]
      · simpa [hi] using hlam1.trans hΛ1
  · simp only [cylinderCoefficient, hx]
    have hdiag : (1 : Mat d).IsHermitian := by simp [Matrix.IsHermitian]
    refine ⟨hdiag, ?_⟩
    intro ξ
    have hone : (1 : Mat d) = Matrix.diagonal (fun _ : Fin d => (1 : ℝ)) := by
      ext i j
      simp
    rw [hone]
    apply polynomialDiagonal_quadratic_bounds
    · intro i
      exact hlam1
    · intro i
      exact hΛ1

end

end CoarseDeGiorgi.SharpnessExamples
