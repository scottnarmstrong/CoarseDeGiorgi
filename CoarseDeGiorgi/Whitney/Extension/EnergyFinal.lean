module

public import CoarseDeGiorgi.Whitney.Extension.EnergySum
public import CoarseDeGiorgi.Whitney.Extension.EnergyScale
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm

/-!
# The scale estimate `e.extension.scale`
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem eLpNorm_sq_eq {τ : ℝ} (hτ : 0 ≤ τ) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ))
    {b : ℝ} (hb : 0 < b) :
    eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ) ^ 2 =
      (∫⁻ x, ENNReal.ofReal (|f x| ^ b) ∂surfaceMeasure τ) ^ (2 / b) := by
  have hm := (integrable_of_continuousOn hτ hf).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hb.le]
  have : ∀ x, ‖f x‖ₑ ^ b = ENNReal.ofReal (|f x| ^ b) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hb.le]
  simp only [this]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  field_simp

theorem fracSeminorm_sq_eq {τ α ξ : ℝ} (hξ : 0 < ξ) (f : Vec d → ℝ) :
    surfaceFracSeminorm τ α ξ f ^ 2 =
      (∫⁻ p, fracKernelWithDimension ((d : ℝ) - 1) α ξ f p
        ∂((surfaceMeasure τ).prod (surfaceMeasure τ))) ^ (2 / ξ) := by
  unfold surfaceFracSeminorm
  rw [ENNReal.rpow_eq_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  field_simp

theorem energy_final (hd : 1 ≤ d) {α ξ : ℝ} (hα : 0 < α) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {τ : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {h : ℝ} (_hh : 0 < h)
      (_hh1 : h ≤ 1) {f : Vec d → ℝ} (_hf : ContinuousOn f (cubeSurface τ)) (j : ℕ) (b : ℝ),
      (b = 2 ∨ b = ξ) →
      ∑' cell : whitneySimplicesNearSize (d := d) τ h j,
          ∫⁻ x in exteriorCellSet cell.1,
            ENNReal.ofReal (vecNormSq (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤
        ENNReal.ofReal Cr * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
          (ENNReal.ofReal ((3 : ℝ) ^ (j : ℤ) *
              (3 : ℝ) ^ (-((j : ℝ) * (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2))))) *
            surfaceFracSeminorm τ α ξ f) ^ 2 +
        ENNReal.ofReal Cr * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
          (ENNReal.ofReal (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) * (((d : ℝ) - 1) * (1 / b - 1 / 2)))) *
            eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ)) ^ 2 := by
  have hξ0 : 0 < ξ := by linarith only [hξ]
  set Nr : ℝ := (overlapN d : ℝ) with hNr
  have hNr0 : 0 ≤ Nr := Nat.cast_nonneg _
  set c : ℝ := (Fintype.card ((Fin d → Fin 3) × Equiv.Perm (Fin d)) : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  obtain ⟨κ2, hκ2, s2⟩ := Ra_scale hd (b := 2) (by norm_num) Nr hNr0
  obtain ⟨κξ, hκξ, sξ⟩ := Ra_scale hd (b := ξ) hξ0 Nr hNr0
  obtain ⟨κB, hκB, sB⟩ := Rb_scale hd (α := α) hξ0 Nr hNr0
  refine ⟨c * max κ2 (max κξ κB), by positivity, ?_⟩
  intro τ hτ0 hτ1 h hh hh1 f hf j b hb
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  obtain ⟨κa, hκa, sa, hκa_le⟩ : ∃ κa : ℝ, 0 ≤ κa ∧ (∀ (j : ℕ) {h : ℝ}, 0 < h →
      Ra d b ((3 : ℝ) ^ ((1 : ℤ) - (j : ℤ))) h * Nr ^ (2 / b) =
        κa * (3 : ℝ) ^ (-(j : ℤ)) *
          (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) * (((d : ℝ) - 1) * (1 / b - 1 / 2)))) ^ 2) ∧
      κa ≤ max κ2 (max κξ κB) := by
    rcases hb with hb' | hb'
    · exact ⟨κ2, hκ2, by rw [hb']; exact s2, le_max_left _ _⟩
    · exact ⟨κξ, hκξ, by rw [hb']; exact sξ, (le_max_left _ _).trans (le_max_right _ _)⟩
  have hb1 : 1 ≤ b := by rcases hb with hb' | hb' <;> rw [hb'] <;> linarith only [hξ]
  have hb2 : b ≤ 2 := by
    rcases hb with rfl | rfl
    · exact le_rfl
    · exact hξ2
  have hb0 : 0 < b := by linarith only [hb1]
  have hsum := sum_energy_le hd hτ0 hτ1 hh hh1 hf hα hξ hξ2 hb1 hb2 j
  refine hsum.trans ?_
  set ℓ : ℝ := (3 : ℝ) ^ ((1 : ℤ) - (j : ℤ)) with hℓ
  set t : ℝ := (3 : ℝ) ^ (-(j : ℤ)) with ht
  set X1 : ℝ := (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-((j : ℝ) * (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2)))) with hX1
  set X2 : ℝ := h⁻¹ * (3 : ℝ) ^ ((j : ℝ) * (((d : ℝ) - 1) * (1 / b - 1 / 2))) with hX2
  have hcard : (Fintype.card ((Fin d → Fin 3) × Equiv.Perm (Fin d)) : ℝ≥0∞) = ENNReal.ofReal c := by
    rw [hc, ENNReal.ofReal_natCast]
  have hN : (overlapN d : ℝ≥0∞) = ENNReal.ofReal Nr := by rw [hNr, ENNReal.ofReal_natCast]
  have hRa := Ra_pos hd (b := b) (ℓ := ℓ) (zpow_pos (by norm_num) _) hh
  have hRb := Rb_pos hd (α := α) (ξ := ξ) (ℓ := ℓ) (zpow_pos (by norm_num) _)
  have hE := eLpNorm_sq_eq hτ hf hb0
  have hF := fracSeminorm_sq_eq (τ := τ) (α := α) hξ0 f
  rw [hcard, hN, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← hE, ← hF,
    ENNReal.ofReal_rpow_of_nonneg hNr0 (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hNr0 (by positivity)]
  have ht0 : 0 < t := zpow_pos (by norm_num) _
  have hX1 : 0 ≤ X1 := by positivity
  have hX2 : 0 ≤ X2 := by positivity
  have e1 : ENNReal.ofReal c * (ENNReal.ofReal (Ra d b ℓ h) *
      (ENNReal.ofReal (Nr ^ (2 / b)) * eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ) ^ 2)) =
      ENNReal.ofReal (c * κa) * ENNReal.ofReal t *
        (ENNReal.ofReal X2 * eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ)) ^ 2 := by
    have h1 : Ra d b ℓ h * Nr ^ (2 / b) = κa * t * X2 ^ 2 := sa j hh
    rw [← mul_assoc (ENNReal.ofReal (Ra d b ℓ h)), ← ENNReal.ofReal_mul hRa.le, h1,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hκa,
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow hX2, mul_pow]
    ring
  have e2 : ENNReal.ofReal c * (ENNReal.ofReal (Rb d α ξ ℓ) *
      (ENNReal.ofReal (Nr ^ (2 / ξ)) * surfaceFracSeminorm τ α ξ f ^ 2)) =
      ENNReal.ofReal (c * κB) * ENNReal.ofReal t *
        (ENNReal.ofReal X1 * surfaceFracSeminorm τ α ξ f) ^ 2 := by
    have h1 : Rb d α ξ ℓ * Nr ^ (2 / ξ) = κB * t * X1 ^ 2 := sB j
    rw [← mul_assoc (ENNReal.ofReal (Rb d α ξ ℓ)), ← ENNReal.ofReal_mul hRb.le, h1,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hκB,
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow hX1, mul_pow]
    ring
  rw [mul_add, e1, e2, add_comm]
  have hM1 : c * κa ≤ c * max κ2 (max κξ κB) := mul_le_mul_of_nonneg_left hκa_le hc0
  have hM2 : c * κB ≤ c * max κ2 (max κξ κB) :=
    mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) hc0
  gcongr

end

end CoarseDeGiorgi.WhitneyExt
