import CoarseDeGiorgi.Endpoint.Rescaling.CellRefinement
import CoarseDeGiorgi.Statements.UpperResponseSpec
import CoarseDeGiorgi.Statements.LowerResponseInvSpec
import CoarseDeGiorgi.Weighted.UpperSpecNorm
import CoarseDeGiorgi.LowerFractional.Restriction
import Mathlib.Analysis.MeanInequalitiesPow

/-! Finite refinement estimates shared by the upper and inverse lower responses. -/

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint.Rescaling

open Foundations.Simplex

theorem norm_le_norm_of_psd_sub {d : ℕ} {A B : Mat d} (hA : A.PosSemidef)
    (hBA : (B - A).PosSemidef) : ‖A‖ ≤ ‖B‖ := by
  apply Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic hA
  intro e
  have h := hBA.dotProduct_mulVec_nonneg e
  have he : vecDot e (matVecMul (B - A) e) =
      vecDot e (matVecMul B e) - vecDot e (matVecMul A e) := by
    simp only [vecDot, matVecMul, Matrix.sub_apply, sub_mul,
      Finset.sum_sub_distrib, mul_sub]
  change 0 ≤ vecDot e (matVecMul (B - A) e) at h
  rw [he] at h
  exact sub_nonneg.mp h

theorem sum_injective_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (g : κ → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (∑ i, g (f i)) ≤ ∑ i, g i := by
  classical
  apply Finset.sum_le_sum_of_injOn f
    (fun _ _ _ _ h => hf h) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => le_rfl) (fun i _ _ => hg i)

theorem finite_power_mean {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {p : ℝ} (hp : 1 ≤ p) :
    Real.rpow ((∑ i, f i) / Fintype.card ι) p ≤
      (∑ i, Real.rpow (f i) p) / Fintype.card ι := by
  classical
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∑ _i : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) f
    (fun _ _ => inv_nonneg.mpr hN.le) hw (fun i _ => hf i) hp
  simp only [← Finset.mul_sum] at h
  simpa only [div_eq_mul_inv, mul_comm, Real.rpow_eq_pow] using h

theorem unit_simplex_subset {d : ℕ} (π : Equiv.Perm (Fin d)) :
    kuhnSimplex 0 π 0 ⊆ originCube 1 := by
  intro x hx
  simpa only [simplexCube, mem_ofPred_eq, zpow_zero, Pi.zero_apply, sub_zero,
    CoarseDeGiorgi.originCube, neg_div] using hx.1

theorem refinement_volume_ratio {d : ℕ} (π : Equiv.Perm (Fin d))
    (η : RefinementIndex 1 π) :
    (volume (simplexCell 1 η.1)).toReal / (volume (kuhnSimplex 0 π 0)).toReal =
      ((3 : ℝ) ^ d)⁻¹ := by
  rw [Assembly.ClassicalMomentsImpl.simplexCell_volume_real, Moments.triangulation_card,
    volume_kuhnSimplex, ENNReal.toReal_div]
  simp only [zero_mul, zpow_zero, ENNReal.ofReal_one, ENNReal.toReal_one, ENNReal.toReal_natCast,
    Nat.one_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hf : (Nat.factorial d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  field_simp

/-- A positive semidefinite response on a parent is bounded by all level-one responses.
The matrix inequality is supplied by a subadditivity hypothesis at the call site. -/
theorem refined_norm_le {d : ℕ} (π : Equiv.Perm (Fin d)) (A : Mat d)
    (B : SimplexIndex d 1 → Mat d) (hA : A.PosSemidef)
    (hagg : (∑' η : RefinementIndex 1 π,
      ((volume (simplexCell 1 η.1)).toReal / (volume (kuhnSimplex 0 π 0)).toReal) •
        B η.1 - A).PosSemidef) :
    ‖A‖ ≤ ((3 : ℝ) ^ d)⁻¹ * ∑ η : SimplexIndex d 1, ‖B η‖ := by
  classical
  have h := norm_le_norm_of_psd_sub hA hagg
  rw [tsum_fintype] at h
  simp only [refinement_volume_ratio] at h
  calc
    ‖A‖ ≤ ‖∑ η : RefinementIndex 1 π, ((3 : ℝ) ^ d)⁻¹ • B η.1‖ := h
    _ ≤ ∑ η : RefinementIndex 1 π, ‖((3 : ℝ) ^ d)⁻¹ • B η.1‖ := norm_sum_le _ _
    _ = ((3 : ℝ) ^ d)⁻¹ * ∑ η : RefinementIndex 1 π, ‖B η.1‖ := by
      simp only [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ((3 : ℝ) ^ d)⁻¹),
        Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_injective_le Subtype.val Subtype.val_injective (fun η => ‖B η‖)
        (fun _ => norm_nonneg _)) (by positivity)

end CoarseDeGiorgi.Endpoint.Rescaling
