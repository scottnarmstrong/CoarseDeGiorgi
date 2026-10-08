module

public import CoarseDeGiorgi.NegSobolev.GaussianMatrix
public import CoarseDeGiorgi.Weighted.UpperSpecNorm

/-! # Quadratic-form comparisons for positive matrix averages -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- Scalar multiplication commutes with the quadratic form. -/
theorem quadratic_smul {d : ℕ} (c : ℝ) (A : Mat d) (e : Vec d) :
    dotProduct e ((c • A).mulVec e) = c * dotProduct e (A.mulVec e) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A bounded nonnegative scalar weight gives an operator norm bound for its matrix integral.
The comparison uses positive semidefiniteness, so it compares the average matrix rather
than the average of its norm. -/
theorem norm_weighted_integral_le {d : ℕ} {μ : Measure (Vec d)}
    (b : Vec d → Mat d) (hb : ∀ i j, Integrable (fun y => b y i j) μ)
    (hpos : ∀ᵐ y ∂μ, (b y).PosSemidef)
    (w : Vec d → ℝ) (hw : AEStronglyMeasurable w μ) (L : ℝ) (hL : 0 ≤ L)
    (hw0 : ∀ᵐ y ∂μ, 0 ≤ w y) (hwL : ∀ᵐ y ∂μ, w y ≤ L) :
    ‖Matrix.of fun i j => ∫ y, w y * b y i j ∂μ‖ ≤
      L * ‖Matrix.of fun i j => ∫ y, b y i j ∂μ‖ := by
  have hwb (i j : Fin d) : Integrable (fun y => w y * b y i j) μ := by
    apply (hb i j).bdd_mul hw
    filter_upwards [hw0, hwL] with y h0 hle
    rwa [Real.norm_of_nonneg h0]
  have hwpos : ∀ᵐ y ∂μ, (w y • b y).PosSemidef := by
    filter_upwards [hw0, hpos] with y h0 hy
    exact hy.smul h0
  have hq (e : Vec d) := quadratic_integrable b hb e
  have hqw (e : Vec d) := quadratic_integrable (fun y => w y • b y) hwb e
  have hnorm : ‖L • (Matrix.of fun i j => ∫ y, b y i j ∂μ)‖ =
      L * ‖Matrix.of fun i j => ∫ y, b y i j ∂μ‖ := by
    rw [norm_smul, Real.norm_of_nonneg hL]
  rw [← hnorm]
  apply Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic
    (integral_matrix_posSemidef (fun y => w y • b y) hwb hwpos)
  intro e
  change dotProduct e ((Matrix.of fun i j => ∫ y, w y * b y i j ∂μ).mulVec e) ≤
    dotProduct e ((L • (Matrix.of fun i j => ∫ y, b y i j ∂μ)).mulVec e)
  have hquad := quadratic_integral_eq (fun y => w y • b y) hwb e
  simp only [Matrix.smul_apply, smul_eq_mul] at hquad
  rw [hquad,
    quadratic_smul, quadratic_integral_eq b hb e, ← integral_const_mul]
  apply integral_mono_ae (hqw e) ((hq e).const_mul L)
  filter_upwards [hpos, hwL] with y hy hle
  rw [quadratic_smul]
  exact mul_le_mul_of_nonneg_right hle (hy.dotProduct_mulVec_nonneg e)

/-- Dropping the complement of a cell in a positive matrix integral gives the
lower bound needed in `p.besov.averages`. -/
theorem norm_integral_restrict_le_weighted {d : ℕ} {μ : Measure (Vec d)}
    (U : Set (Vec d))
    (b : Vec d → Mat d) (hb : ∀ i j, Integrable (fun y => b y i j) μ)
    (hpos : ∀ᵐ y ∂μ, (b y).PosSemidef)
    (w : Vec d → ℝ) (hwb : ∀ i j, Integrable (fun y => w y * b y i j) μ)
    (hw0 : ∀ᵐ y ∂μ, 0 ≤ w y) (L : ℝ) (hL : 0 ≤ L)
    (hwL : ∀ᵐ y ∂(μ.restrict U), L ≤ w y) :
    L * ‖Matrix.of fun i j => ∫ y in U, b y i j ∂μ‖ ≤
      ‖Matrix.of fun i j => ∫ y, w y * b y i j ∂μ‖ := by
  have hposU := ae_restrict_of_ae hpos (s := U)
  have hIU := integral_matrix_posSemidef b (fun i j => (hb i j).restrict) hposU
  rw [← Real.norm_of_nonneg hL, ← norm_smul]
  apply Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic (hIU.smul hL)
  intro e
  change dotProduct e ((L • (Matrix.of fun i j => ∫ y in U, b y i j ∂μ)).mulVec e) ≤
    dotProduct e ((Matrix.of fun i j => ∫ y, w y * b y i j ∂μ).mulVec e)
  have hquad := quadratic_integral_eq (fun y => w y • b y) hwb e
  simp only [Matrix.smul_apply, smul_eq_mul] at hquad
  rw [quadratic_smul, quadratic_integral_eq b (fun i j => (hb i j).restrict) e,
    hquad, ← integral_const_mul]
  have hq := quadratic_integrable b hb e
  have hqw := quadratic_integrable (fun y => w y • b y) hwb e
  have hqw0 : ∀ᵐ y ∂μ, 0 ≤ dotProduct e ((w y • b y).mulVec e) := by
    filter_upwards [hw0, hpos] with y h0 hy
    rw [quadratic_smul]
    exact mul_nonneg h0 (hy.dotProduct_mulVec_nonneg e)
  calc
    _ ≤ ∫ y in U, dotProduct e ((w y • b y).mulVec e) ∂μ := by
      apply integral_mono_ae ((hq.restrict).const_mul L) (hqw.restrict)
      filter_upwards [hwL, hposU] with y hle hy
      rw [quadratic_smul]
      exact mul_le_mul_of_nonneg_right hle (hy.dotProduct_mulVec_nonneg e)
    _ ≤ _ := setIntegral_le_integral hqw hqw0

end CoarseDeGiorgi.NegSobolev
