import CoarseDeGiorgi.Whitney.Extension.Properties

/-!
# Linearity of `f ↦ L_h f`
-/

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem vecDot_lin (c₁ c₂ : ℝ) (e₁ e₂ x : Vec d) :
    vecDot (fun i => c₁ * e₁ i + c₂ * e₂ i) x = c₁ * vecDot e₁ x + c₂ * vecDot e₂ x := by
  simp only [vecDot, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem freeValue_linear (hτ : 0 ≤ τ) {f₁ f₂ : Vec d → ℝ} (h₁ : ContinuousOn f₁ (cubeSurface τ))
    (h₂ : ContinuousOn f₂ (cubeSurface τ)) (c₁ c₂ : ℝ) (z : {z : Vec d // IsFreeVertex τ z}) :
    whitneyFreeValue τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) z =
      c₁ * whitneyFreeValue τ h f₁ z + c₂ * whitneyFreeValue τ h f₂ z := by
  simp only [whitneyFreeValue_eq, patchAvg]
  rw [average_linear _ (integrable_of_continuousOn hτ h₁) (integrable_of_continuousOn hτ h₂)]
  ring

theorem ext_linear (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {f₁ f₂ : Vec d → ℝ}
    (h₁ : ContinuousOn f₁ (cubeSurface τ)) (h₂ : ContinuousOn f₂ (cubeSurface τ)) (c₁ c₂ : ℝ)
    {x : Vec d} (hx : x ∈ (closedReferenceCube (d := d) τ)ᶜ) :
    whitneyAffineExtension τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) hτ0 hτ1 x =
      c₁ * whitneyAffineExtension τ h f₁ hτ0 hτ1 x +
        c₂ * whitneyAffineExtension τ h f₂ hτ0 hτ1 x := by
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  have hI₁ := interp_spec (h := h) hτ0 hτ1 f₁
  have hI₂ := interp_spec (h := h) hτ0 hτ1 f₂
  have hcont : ContinuousOn (fun x => c₁ * whitneyAffineExtension τ h f₁ hτ0 hτ1 x +
      c₂ * whitneyAffineExtension τ h f₂ hτ0 hτ1 x) (closedReferenceCube (d := d) τ)ᶜ :=
    (continuousOn_const.mul hI₁.2.1).add (continuousOn_const.mul hI₂.2.1)
  have haff : ∀ cell : ExteriorCell d τ, ∃ (e : Vec d) (c : ℝ),
      ∀ x ∈ exteriorCellSet cell, (c₁ * whitneyAffineExtension τ h f₁ hτ0 hτ1 x +
        c₂ * whitneyAffineExtension τ h f₂ hτ0 hτ1 x) = vecDot e x + c := by
    intro cell
    obtain ⟨e₁, k₁, he₁⟩ := hI₁.2.2.1 cell
    obtain ⟨e₂, k₂, he₂⟩ := hI₂.2.2.1 cell
    refine ⟨fun i => c₁ * e₁ i + c₂ * e₂ i, c₁ * k₁ + c₂ * k₂, fun y hy => ?_⟩
    rw [he₁ y hy, he₂ y hy, vecDot_lin]
    ring
  have hvals : ∀ z : {z : Vec d // IsFreeVertex τ z},
      (c₁ * whitneyAffineExtension τ h f₁ hτ0 hτ1 z.1 +
        c₂ * whitneyAffineExtension τ h f₂ hτ0 hτ1 z.1) =
        whitneyFreeValue τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) z := by
    intro z
    rw [hI₁.2.2.2 z, hI₂.2.2.2 z, freeValue_linear hτ h₁ h₂]
  have hu := (C32_spec hτ0 hτ1 (interp_spec (h := h) hτ0 hτ1
    (fun y => c₁ * f₁ y + c₂ * f₂ y))).1 _ hcont haff hvals hx
  exact hu.symm

end

end CoarseDeGiorgi.WhitneyExt
