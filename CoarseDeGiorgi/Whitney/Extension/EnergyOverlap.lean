module

public import CoarseDeGiorgi.Whitney.Extension.EnergyCube
public import CoarseDeGiorgi.Whitney.Extension.Overlap

/-!
# Bounded overlap of the patches `Σ_D` at one scale
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

/-- The overlap count of the patches `Σ_D`. -/
def overlapN (d : ℕ) : ℕ := (2 * ⌈10 * Real.sqrt (d : ℝ)⌉₊ + 1) ^ d

theorem center_sub_le (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {x : Vec d} (hx : x ∈ sigmaD τ D) (i : Fin d) :
    |(D.index i : ℝ) * cubeScaleFactor D - x i| ≤ 10 * Real.sqrt (d : ℝ) * cubeScaleFactor D := by
  have hp := cubeScaleFactor_pos D
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hdr
  have hc : triadicCenter D ∈ closedTriadicCube D := fun i => by
    simp only [sub_self, abs_zero]; linarith only [hp]
  have h1 := hx.2
  simp only [mem_ofPred_eq] at h1
  have h2 : ‖triadicCenter D - seedProjection τ (triadicCenter D)‖ ≤ 9 * cubeScaleFactor D := by
    refine (norm_sub_seedProjection_le (by linarith only [hτ0]) _).trans ?_
    exact max_le (by linarith only [hp]) (gap_upper hτ0 hτ1 hD hc)
  have h3 : ‖seedProjection τ (triadicCenter D) - x‖ ≤ euclidDist x (seedProjection τ (triadicCenter D)) := by
    rw [norm_sub_rev]; exact norm_sub_le_euclidDist _ _
  have h4 : ‖triadicCenter D - x‖ ≤ 9 * cubeScaleFactor D +
      Real.sqrt (d : ℝ) * cubeScaleFactor D := by
    have := norm_add_le (triadicCenter D - seedProjection τ (triadicCenter D))
      (seedProjection τ (triadicCenter D) - x)
    rw [sub_add_sub_cancel] at this
    linarith only [this, h2, h3, h1]
  have h5 : |triadicCenter D i - x i| ≤ ‖triadicCenter D - x‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (triadicCenter D - x) i
  have h6 : (D.index i : ℝ) * cubeScaleFactor D = triadicCenter D i := rfl
  rw [h6]
  nlinarith [h4, h5, hs1, hp]

/-- Distinct cubes of one scale have boundedly overlapping patches. -/
theorem sigmaD_overlap (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {ι : Type*}
    (D : ι → TriadicCube d) (hDW : ∀ i, D i ∈ whitneyCubes (d := d) τ) (s : ℤ)
    (hs : ∀ i, (D i).scale = s) (hinj : Function.Injective D) (x : Vec d) (T : Finset ι)
    (hT : ∀ i ∈ T, x ∈ sigmaD τ (D i)) : T.card ≤ overlapN d := by
  classical
  set ℓ : ℝ := (3 : ℝ) ^ s with hℓ
  have hℓp : 0 < ℓ := zpow_pos (by norm_num) _
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by linarith only [hdr])
  have hsc : ∀ i, cubeScaleFactor (D i) = ℓ := fun i => by
    unfold cubeScaleFactor; rw [hs i]
  have hinj' : Function.Injective (fun i => (D i).index) := by
    intro i i' hii
    apply hinj
    have key : ∀ A B : TriadicCube d, A.scale = B.scale → A.index = B.index → A = B := by
      intro A B h1 h2; cases A; cases B; simp_all
    exact key _ _ ((hs i).trans (hs i').symm) hii
  have hcard : (T.image (fun i => (D i).index)).card = T.card :=
    Finset.card_image_of_injective _ hinj'
  have := card_le_of_lattice (d := d) hℓp (R := 10 * Real.sqrt (d : ℝ) * ℓ) (by positivity) x
    (T.image (fun i => (D i).index)) (by
      intro m hm k
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      have := center_sub_le hd hτ0 hτ1 (hDW i) (hT i hi) k
      rwa [hsc i] at this)
  rw [hcard, mul_div_cancel_right₀ _ hℓp.ne'] at this
  exact this

end

end CoarseDeGiorgi.WhitneyExt
