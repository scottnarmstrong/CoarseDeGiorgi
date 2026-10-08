module

public import CoarseDeGiorgi.Whitney.Extension.LipConj

/-! # Finiteness of the Lipschitz constant of the affine extension

The construction needs only `0 < h ≤ 1`, so it also applies at the wider widths
of `p.affine.extension`. Compactness bounds the boundary data, and the existing
Euclidean difference estimate gives a finite exterior Lipschitz constant.
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

theorem exists_extension_lipConst_lt_top {d : ℕ} {τ h : ℝ} (hd : 1 ≤ d)
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h) (hh1 : h ≤ 1)
    {f : Vec d → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (cubeSurface τ)) :
    ∃ F : Vec d → ℝ,
      (∀ x ∈ (closedReferenceCube (d := d) τ)ᶜ,
        F x = whitneyAffineExtension τ h f hτ0 hτ1 x) ∧
      (∀ y ∈ cubeSurface (d := d) τ, F y = f y) ∧
      euclidLipConst (originCube (d := d) τ)ᶜ F < ⊤ := by
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  obtain ⟨B, hB⟩ := (isCompact_cubeSurface τ).exists_bound_of_continuousOn hf.continuousOn
  have hbd : ∀ᵐ y ∂surfaceMeasure τ, |f y| ≤ max B 0 :=
    (surfaceMeasure_ae_mem τ hτ).mono fun y hy =>
      (show |f y| ≤ B by simpa only [Real.norm_eq_abs] using hB y hy).trans
        (le_max_left _ _)
  have hLip : ∀ x ∈ cubeSurface τ, ∀ y ∈ cubeSurface τ,
      |f x - f y| ≤ (K : ℝ) * euclidDist x y := by
    intro x hx y hy
    have hxy := hf.dist_le_mul x hx y hy
    rw [Real.dist_eq, dist_eq_norm] at hxy
    exact hxy.trans (mul_le_mul_of_nonneg_left (norm_sub_le_euclidDist x y) K.coe_nonneg)
  obtain ⟨F, hF1, hF2, hF3⟩ := exists_lipschitz_extension hd hτ0 hτ1 hh hh1
    hf.continuousOn K.coe_nonneg (le_max_right B 0) hLip hbd
  refine ⟨F, hF1, hF2, lt_of_le_of_lt (euclidLipConst_le_of_bound
    (M := LipConst d * ((K : ℝ) + max B 0 / h)) ?_ ?_) ENNReal.ofReal_lt_top⟩
  · exact mul_nonneg (LipConst_pos d hd).le (add_nonneg K.coe_nonneg
      (div_nonneg (le_max_right B 0) hh.le))
  · intro x hx y hy
    exact hF3 x y (norm_ge_of_notMem_originCube τ hτ hx)
      (norm_ge_of_notMem_originCube τ hτ hy)

end CoarseDeGiorgi.WhitneyExt
