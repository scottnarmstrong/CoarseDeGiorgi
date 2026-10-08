import CoarseDeGiorgi.Foundations.Reconstruction.LowestScaling
import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicFields

/-! # Scale-uniform bounds on the lowest kernel and its derivatives -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Compactness of one period bounds the first three unit-side jets. -/
theorem exists_bound_unitLowestKernel : ∃ A : ℝ, 1 ≤ A ∧
    ∀ i ≤ 2, ∀ x : Vec d, ‖iteratedFDeriv ℝ i (lowestKernel 1 d) x‖ ≤ A :=
  exists_bound_periodicField_jets 1 (lowestKernel 1 d) (contDiff_lowestKernel 1 d)
    (lowestKernel_add_period 1 d) 2

/-- Physical rescaling introduces one inverse length for each derivative. -/
theorem norm_iteratedFDeriv_lowestKernel_le (m : ℤ) {A : ℝ} (i : ℕ)
    (hA : ∀ x : Vec d, ‖iteratedFDeriv ℝ i (lowestKernel 1 d) x‖ ≤ A) (v : Vec d) :
    ‖iteratedFDeriv ℝ i (lowestKernel m d) v‖ ≤
      A * auxSide m * ((auxSide m) ^ d)⁻¹ * ((auxSide m)⁻¹) ^ i := by
  have hm := auxSide_pos m
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  let L : Vec d →L[ℝ] Vec d := (auxSide m)⁻¹ • ContinuousLinearMap.id ℝ (Vec d)
  have hL : ‖L‖ ≤ (auxSide m)⁻¹ := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (auxSide_pos m))]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (auxSide_pos m).le)
      ContinuousLinearMap.norm_id_le
  have hc : ContDiff ℝ (⊤ : ℕ∞) (lowestKernel 1 d ∘ L) :=
    (contDiff_lowestKernel 1 d).comp L.contDiff
  have heq : lowestKernel m d = fun x =>
      (auxSide m * ((auxSide m) ^ d)⁻¹) • (lowestKernel 1 d ∘ L) x :=
    funext fun x => lowestKernel_scale m d x
  rw [heq, iteratedFDeriv_const_smul_apply' (hc.contDiffAt.of_le (by simp)),
    L.iteratedFDeriv_comp_right (contDiff_lowestKernel 1 d) v (by simp), norm_smul,
    Real.norm_eq_abs, abs_of_pos (mul_pos (auxSide_pos m)
      (inv_pos.mpr (pow_pos (auxSide_pos m) d)))]
  calc
    _ ≤ (auxSide m * ((auxSide m) ^ d)⁻¹) *
        (‖iteratedFDeriv ℝ i (lowestKernel 1 d) (L v)‖ * ∏ _ : Fin i, ‖L‖) :=
      mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
        (by positivity)
    _ ≤ (auxSide m * ((auxSide m) ^ d)⁻¹) * (A * ((auxSide m)⁻¹) ^ i) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      gcongr
      exact hA (L v)
    _ = _ := by ring

/-- A dimension-only constant bounds all lowest kernels, including orders one and two. -/
theorem exists_bound_lowestKernel_jets : ∃ A : ℝ, 1 ≤ A ∧ ∀ m : ℤ,
    (∀ v : Vec d, ‖lowestKernel m d v‖ ≤ A * auxSide m * ((auxSide m) ^ d)⁻¹) ∧
    (∀ v : Vec d, ‖fderiv ℝ (lowestKernel m d) v‖ ≤ A * ((auxSide m) ^ d)⁻¹) ∧
    (∀ v : Vec d, ‖fderiv ℝ (fderiv ℝ (lowestKernel m d)) v‖ ≤
      A * ((auxSide m) ^ d)⁻¹ * (auxSide m)⁻¹) := by
  obtain ⟨A, hA, hb⟩ := exists_bound_unitLowestKernel (d := d)
  refine ⟨A, hA, fun m => ⟨?_, ?_, ?_⟩⟩
  · intro v
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using
      norm_iteratedFDeriv_lowestKernel_le m 0 (hb 0 (by omega)) v
  · intro v
    have h := norm_iteratedFDeriv_lowestKernel_le m 1 (hb 1 (by omega)) v
    rw [norm_iteratedFDeriv_one, pow_one] at h
    convert h using 1
    field_simp [(auxSide_pos m).ne']
  · intro v
    have h := norm_iteratedFDeriv_lowestKernel_le m 2 (hb 2 le_rfl) v
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at h
    convert h using 1
    field_simp [(auxSide_pos m).ne']

end

end CoarseDeGiorgi.Foundations.Reconstruction
