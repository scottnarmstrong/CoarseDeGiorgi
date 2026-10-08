module

public import CoarseDeGiorgi.Foundations.Reconstruction.Geometry

/-! # Representative invariance and elementary branches of reconstruction -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- Replacing either representative changes the pair kernel only on a product-null set.
No measurability hypothesis on the original representative is required. -/
theorem fracSeminorm_congr_ae {V : Set (Vec d)} {α r : ℝ} {w w' : Vec d → ℝ}
    (h : w =ᵐ[volume.restrict V] w') :
    FracGeometry.fracSeminorm V α r w = FracGeometry.fracSeminorm V α r w' := by
  rw [FracGeometry.fracSeminorm_eq_eFracSeminorm,
    FracGeometry.fracSeminorm_eq_eFracSeminorm]
  unfold Euclid.eFracSeminorm
  congr 1
  apply lintegral_congr_ae
  have hf := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict V) (ν := volume.restrict V)).ae_eq_comp h
  have hs := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict V) (ν := volume.restrict V)).ae_eq_comp h
  filter_upwards [hf, hs] with p hp hq
  simp only [Function.comp_apply] at hp hq
  simp only [Euclid.euclidKernel, hp, hq]

/-- A constant addition cancels exactly in the copied Euclidean pair kernel. -/
theorem fracSeminorm_add_const (V : Set (Vec d)) (α r c : ℝ) (w : Vec d → ℝ) :
    FracGeometry.fracSeminorm V α r (fun x => w x + c) =
      FracGeometry.fracSeminorm V α r w := by
  rw [FracGeometry.fracSeminorm_eq_eFracSeminorm,
    FracGeometry.fracSeminorm_eq_eFracSeminorm]
  unfold Euclid.eFracSeminorm Euclid.euclidKernel
  simp only [add_sub_add_right_eq_sub]

/-- The weak identity is invariant under a.e. replacement of both fields. -/
theorem hasWeakGradientOn_congr_ae {V : Set (Vec d)} {w w' : Vec d → ℝ}
    {Dw Dw' : Vec d → Vec d} (hw : w =ᵐ[volume.restrict V] w')
    (hDw : Dw =ᵐ[volume.restrict V] Dw') (h : HasWeakGradientOn V w Dw) :
    HasWeakGradientOn V w' Dw' := by
  intro i φ hφ hcompact hsupp
  calc
    ∫ x in V, w' x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        ∫ x in V, w x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      rw [hx]
    _ = -∫ x in V, Dw x i * φ x ∂volume := h i φ hφ hcompact hsupp
    _ = -∫ x in V, Dw' x i * φ x ∂volume := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hDw] with x hx
      rw [hx]

/-- The zero-dimensional fractional seminorm vanishes for every positive exponent. -/
theorem fracSeminorm_zero_dim (V : Set (Vec 0)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Vec 0 → ℝ) : FracGeometry.fracSeminorm V α r w = 0 := by
  rw [FracGeometry.fracSeminorm_eq_eFracSeminorm]
  have hk : Euclid.euclidKernel (α * r) r w = fun _ => 0 := by
    funext p
    have hp : p.1 = p.2 := Subsingleton.elim _ _
    simp only [Euclid.euclidKernel, hp, sub_self, abs_zero, Real.zero_rpow hr.ne',
      zero_div, ENNReal.ofReal_zero]
  simp only [Euclid.eFracSeminorm, Nat.cast_zero, zero_add, hk, lintegral_zero,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr)]

/-- The positive constant handles an infinite source series without further inputs. -/
theorem le_of_sourceSeries_eq_top {C : ℝ} (hC : 0 < C) {a b : ℝ≥0∞} (hb : b = ⊤) :
    a ≤ ENNReal.ofReal C * b := by
  rw [hb, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC))]
  exact le_top

end

end CoarseDeGiorgi.Foundations.Reconstruction
