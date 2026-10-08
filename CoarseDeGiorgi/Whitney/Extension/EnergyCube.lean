import CoarseDeGiorgi.Whitney.Extension.EnergyAvg

/-!
# The energy of `L_h f` on the simplices of one selected cube
-/

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem rpow_inv_sq {u b : ℝ} (hu : 0 ≤ u) (hb : 0 < b) : (u ^ b⁻¹) ^ 2 = u ^ (2 / b) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
  congr 1
  push_cast
  field_simp

theorem abs_le_rpow_inv {a u b : ℝ} (hb : 0 < b) (_hu : 0 ≤ u) (h : |a| ^ b ≤ u) :
    |a| ≤ u ^ b⁻¹ := by
  calc |a| = (|a| ^ b) ^ b⁻¹ := (Real.rpow_rpow_inv (abs_nonneg _) hb.ne').symm
    _ ≤ u ^ b⁻¹ := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h (inv_nonneg.mpr hb.le)

theorem add_sq_le' (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - y)]

/-- Constant of the `L^b` term. -/
def Ra (d : ℕ) (b ℓ h : ℝ) : ℝ :=
  2 * (ℓ ^ d * ((C32 d + 1) / ℓ) ^ 2) * (2 * ℓ / h) ^ 2 * ((mLow d ℓ)⁻¹) ^ (2 / b)

/-- Constant of the fractional term. -/
def Rb (d : ℕ) (α ξ ℓ : ℝ) : ℝ :=
  2 * (ℓ ^ d * ((C32 d + 1) / ℓ) ^ 2) *
    (((mLow d ℓ)⁻¹) ^ 2 * (2 * Real.sqrt (d : ℝ) * ℓ) ^ ((d : ℝ) - 1 + α * ξ)) ^ (2 / ξ)

theorem Ra_pos (hd : 1 ≤ d) {b ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) : 0 < Ra d b ℓ h := by
  have := mLow_pos d hℓ hd
  have := C32_nonneg d
  unfold Ra; positivity

theorem Rb_pos (hd : 1 ≤ d) {α ξ ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < Rb d α ξ ℓ := by
  have := mLow_pos d hℓ hd
  have := C32_nonneg d
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by linarith only [hdr])
  unfold Rb; positivity

theorem cell_energy_le (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h)
    (hh1 : h ≤ 1) {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ)
    (hnear : infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) < h)
    {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {α ξ b : ℝ} (hα : 0 < α) (hξ : 1 ≤ ξ)
    (hb : 1 ≤ b) {cell : ExteriorCell d τ} (hc : cell.1.val = D) :
    ∫⁻ x in exteriorCellSet cell,
        ENNReal.ofReal (vecNormSq (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤
      ENNReal.ofReal (Ra d b (cubeScaleFactor D) h) * locMass τ f b D ^ (2 / b) +
        ENNReal.ofReal (Rb d α ξ (cubeScaleFactor D)) * locFrac τ α ξ f D ^ (2 / ξ) := by
  have hp := cubeScaleFactor_pos D
  have hl2 := (near_gap hτ0 hτ1 hD hnear).1
  have hl : cubeScaleFactor D < 1 := by linarith only [hl2, hh1]
  have hb0 : 0 < b := by linarith only [hb]
  have hξ0 : 0 < ξ := by linarith only [hξ]
  set ℓ := cubeScaleFactor D with hℓ
  have hRa := Ra_pos hd (b := b) hp hh
  have hRb := Rb_pos hd (α := α) (ξ := ξ) hp
  by_cases hE : locMass τ f b D = ⊤
  · rw [hE, ENNReal.top_rpow_of_pos (by positivity), ENNReal.mul_top
      (ENNReal.ofReal_pos.mpr hRa).ne', top_add]
    exact le_top
  by_cases hS : locFrac τ α ξ f D = ⊤
  · rw [hS, ENNReal.top_rpow_of_pos (by positivity), ENNReal.mul_top
      (ENNReal.ofReal_pos.mpr hRb).ne', add_top]
    exact le_top
  set e := (locMass τ f b D).toReal with he
  set s := (locFrac τ α ξ f D).toReal with hs
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hee : ENNReal.ofReal e = locMass τ f b D := ENNReal.ofReal_toReal hE
  have hss : ENNReal.ofReal s = locFrac τ α ξ f D := ENNReal.ofReal_toReal hS
  have hm := mLow_pos d hp hd
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by linarith only [hdr])
  set m := mLow d ℓ with hmdef
  set Δ := (2 * Real.sqrt (d : ℝ) * ℓ) ^ ((d : ℝ) - 1 + α * ξ) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  -- bounds for the means
  have hmain : ∀ z z' : {z : Vec d // IsFreeVertex τ z}, z.1 ∈ closedTriadicCube D →
      z'.1 ∈ closedTriadicCube D → |whitneyFreeValue τ h f z - whitneyFreeValue τ h f z'| ≤
        2 * ℓ / h * (m⁻¹ * e) ^ b⁻¹ + (m⁻¹ ^ 2 * Δ * s) ^ ξ⁻¹ := by
    intro z z' hz hz'
    refine (freeValue_sub_le hh f hz hz').trans ?_
    have h1 := avg_rpow_le hd hτ0 hτ1 hD hl hz hf hb
    have h2 := avg_sub_rpow_le hd hτ0 hτ1 hD hl hz hz' hf hα hξ
    have h1' : |patchAvg τ f z.1| ^ b ≤ m⁻¹ * e := by
      have : ENNReal.ofReal (|patchAvg τ f z.1| ^ b) ≤ ENNReal.ofReal (m⁻¹ * e) := by
        refine h1.trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), hee, ENNReal.ofReal_inv_of_pos hm]
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
    have h2' : |patchAvg τ f z.1 - patchAvg τ f z'.1| ^ ξ ≤ m⁻¹ ^ 2 * Δ * s := by
      have : ENNReal.ofReal (|patchAvg τ f z.1 - patchAvg τ f z'.1| ^ ξ) ≤
          ENNReal.ofReal (m⁻¹ ^ 2 * Δ * s) := by
        refine h2.trans (le_of_eq ?_)
        have hmm : (ENNReal.ofReal m * ENNReal.ofReal m)⁻¹ = ENNReal.ofReal (m⁻¹ ^ 2) := by
          rw [← ENNReal.ofReal_mul hm.le, ← ENNReal.ofReal_inv_of_pos (mul_pos hm hm), sq, mul_inv]
        rw [hmm, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hss]
        exact (mul_assoc _ _ _).symm
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
    have h3 := abs_le_rpow_inv hb0 (by positivity) h1'
    have h4 := abs_le_rpow_inv hξ0 (by positivity) h2'
    have : 0 ≤ 2 * ℓ / h := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 this]
  have hcell := cell_lintegral_le hτ0 hτ1 f hD hmain hc
  refine hcell.trans ?_
  set P := 2 * ℓ / h * (m⁻¹ * e) ^ b⁻¹ with hP
  set Q := (m⁻¹ ^ 2 * Δ * s) ^ ξ⁻¹ with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hP2 : P ^ 2 = (2 * ℓ / h) ^ 2 * ((m⁻¹) ^ (2 / b) * e ^ (2 / b)) := by
    rw [hP, mul_pow, rpow_inv_sq (by positivity) hb0, Real.mul_rpow (inv_nonneg.mpr hm.le) he0]
  have hQ2 : Q ^ 2 = (m⁻¹ ^ 2 * Δ) ^ (2 / ξ) * s ^ (2 / ξ) := by
    rw [hQ, rpow_inv_sq (by positivity) hξ0, Real.mul_rpow (by positivity) hs0]
  have hC1 : C32 d / ℓ * (P + Q) ≤ (C32 d + 1) / ℓ * (P + Q) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right (by linarith only) hp.le
  have hreal : ℓ ^ d * (C32 d / ℓ * (P + Q)) ^ 2 ≤
      Ra d b ℓ h * e ^ (2 / b) + Rb d α ξ ℓ * s ^ (2 / ξ) := by
    have h0 : 0 ≤ C32 d / ℓ * (P + Q) := mul_nonneg (div_nonneg (C32_nonneg d) hp.le) (by positivity)
    have h1 : (C32 d / ℓ * (P + Q)) ^ 2 ≤ ((C32 d + 1) / ℓ * (P + Q)) ^ 2 :=
      pow_le_pow_left₀ h0 hC1 2
    have h2 : ((C32 d + 1) / ℓ * (P + Q)) ^ 2 = ((C32 d + 1) / ℓ) ^ 2 * (P + Q) ^ 2 := by ring
    have h3 := add_sq_le' P Q
    have hpow : 0 ≤ ℓ ^ d := by positivity
    have hq : 0 ≤ ((C32 d + 1) / ℓ) ^ 2 := by positivity
    calc ℓ ^ d * (C32 d / ℓ * (P + Q)) ^ 2
        ≤ ℓ ^ d * (((C32 d + 1) / ℓ) ^ 2 * (P + Q) ^ 2) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hpow
      _ ≤ ℓ ^ d * (((C32 d + 1) / ℓ) ^ 2 * (2 * P ^ 2 + 2 * Q ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hq) hpow
      _ = _ := by
          rw [hP2, hQ2]; unfold Ra Rb; ring
  have hRa0 := hRa.le
  have hRb0 := hRb.le
  calc ENNReal.ofReal (ℓ ^ d * (C32 d / ℓ * (2 * ℓ / h * (m⁻¹ * e) ^ b⁻¹ +
        (m⁻¹ ^ 2 * Δ * s) ^ ξ⁻¹)) ^ 2) ≤ ENNReal.ofReal (Ra d b ℓ h * e ^ (2 / b) +
          Rb d α ξ ℓ * s ^ (2 / ξ)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hRa0,
          ENNReal.ofReal_mul hRb0, ← ENNReal.ofReal_rpow_of_nonneg he0 (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hs0 (by positivity), hee, hss]

end

end CoarseDeGiorgi.WhitneyExt
