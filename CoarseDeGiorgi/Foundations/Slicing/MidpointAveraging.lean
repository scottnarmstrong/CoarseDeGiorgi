module

public import CoarseDeGiorgi.Foundations.FracGeometry.TranslationEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Midpoint averaging with constants depending only on dimension. -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Slicing

open Homogenization MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

/-- Open Euclidean ball on the coordinate carrier. -/
def euclidBall {d : ℕ} (x : Vec d) (R : ℝ) : Set (Vec d) :=
  {z | Euclid.eDist2 x z < R}

/-- The power of the difference appearing in both fractional kernels. -/
def differencePower {d : ℕ} (r : ℝ) (F : Vec d → ℝ) (x z : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (|F x - F z| ^ r)

theorem measurableSet_euclidBall {d : ℕ} (x : Vec d) (R : ℝ) :
    MeasurableSet (euclidBall x R) :=
  measurableSet_lt (Euclid.continuous_eDist2.measurable.comp
    (measurable_const.prodMk measurable_id)) measurable_const

theorem measurable_differencePower {d : ℕ} (r : ℝ) {F : Vec d → ℝ}
    (hF : Measurable F) (x : Vec d) : Measurable (differencePower r F x) := by
  change Measurable (fun z : Vec d => ENNReal.ofReal (|F x - F z| ^ r))
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    (((measurable_const.sub hF).norm.pow measurable_const).ennreal_ofReal :
      Measurable (fun z => ENNReal.ofReal (‖F x - F z‖ ^ r)))

private theorem eDist2_midpoint {d : ℕ} (x y : Vec d) :
    Euclid.eDist2 x ((1 / 2 : ℝ) • (x + y)) = (1 / 2 : ℝ) * Euclid.eDist2 x y := by
  unfold Euclid.eDist2
  rw [show x - (1 / 2 : ℝ) • (x + y) = (1 / 2 : ℝ) • (x - y) by module]
  rw [Euclid.eNorm2_smul]
  norm_num

private theorem eNorm2_le_dimension_mul {d : ℕ} (v : Vec d) :
    Euclid.eNorm2 v ≤ ((d : ℝ) + 1) * ‖v‖ := by
  have hsq : Real.sqrt (d : ℝ) ≤ (d : ℝ) + 1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith only [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact (Euclid.eNorm2_le_sqrt_mul_norm v).trans
    (mul_le_mul_of_nonneg_right hsq (norm_nonneg v))

/-- The midpoint cube lies in both Euclidean balls of radius `|x-y|`. -/
theorem midpoint_ball_subset {d : ℕ} {x y : Vec d} (hxy : x ≠ y) :
    ball ((1 / 2 : ℝ) • (x + y)) (Euclid.eDist2 x y / (2 * ((d : ℝ) + 1))) ⊆
      euclidBall x (Euclid.eDist2 x y) ∩ euclidBall y (Euclid.eDist2 x y) := by
  have hℓ : 0 < Euclid.eDist2 x y := Euclid.eDist2_pos hxy
  have hdim : 0 < (d : ℝ) + 1 := by positivity
  have hsym : Euclid.eDist2 y x = Euclid.eDist2 x y := by
    simp only [Euclid.eDist2, Euclid.eNorm2_eq_norm_toLp, WithLp.toLp_sub, norm_sub_rev]
  intro z hz
  have hzdist : ‖(1 / 2 : ℝ) • (x + y) - z‖ <
      Euclid.eDist2 x y / (2 * ((d : ℝ) + 1)) := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hz
  have hsmall : Euclid.eDist2 ((1 / 2 : ℝ) • (x + y)) z < Euclid.eDist2 x y / 2 := by
    calc
      _ ≤ ((d : ℝ) + 1) * ‖(1 / 2 : ℝ) • (x + y) - z‖ := eNorm2_le_dimension_mul _
      _ < ((d : ℝ) + 1) * (Euclid.eDist2 x y / (2 * ((d : ℝ) + 1))) :=
        mul_lt_mul_of_pos_left hzdist hdim
      _ = _ := by field_simp
  have hxmid := eDist2_midpoint x y
  have hymid : Euclid.eDist2 y ((1 / 2 : ℝ) • (x + y)) =
      (1 / 2 : ℝ) * Euclid.eDist2 x y := by
    rw [add_comm x y, eDist2_midpoint y x, hsym]
  constructor
  · change Euclid.eDist2 x z < Euclid.eDist2 x y
    have htri := Euclid.eDist2_triangle x ((1 / 2 : ℝ) • (x + y)) z
    linarith only [htri, hxmid, hsmall]
  · change Euclid.eDist2 y z < Euclid.eDist2 x y
    have htri := Euclid.eDist2_triangle y ((1 / 2 : ℝ) • (x + y)) z
    linarith only [htri, hymid, hsmall]

/-- Midpoint averaging costs `2^r` and a dimension-only factor, with no extra
exponent in the latter. -/
theorem differencePower_le_midpoint_average {d : ℕ} {r : ℝ} (hr : 0 < r)
    {F : Vec d → ℝ} (hF : Measurable F) {x y : Vec d} (hxy : x ≠ y) :
    differencePower r F x y ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ d) * (2 : ℝ≥0∞) ^ r *
        ENNReal.ofReal (Euclid.eDist2 x y ^ (-(d : ℝ))) *
        ((∫⁻ z in euclidBall x (Euclid.eDist2 x y), differencePower r F x z) +
          ∫⁻ z in euclidBall y (Euclid.eDist2 x y), differencePower r F y z) := by
  let ℓ := Euclid.eDist2 x y
  let B := ball ((1 / 2 : ℝ) • (x + y)) (ℓ / (2 * ((d : ℝ) + 1)))
  have hℓ : 0 < ℓ := Euclid.eDist2_pos hxy
  have hR : 0 < ℓ / (2 * ((d : ℝ) + 1)) := by positivity
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume _ hR).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have htwo : (2 : ℝ≥0∞) ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr.le (by norm_num)
  have hpoint (z : Vec d) : differencePower r F x y ≤ (2 : ℝ≥0∞) ^ r *
      (differencePower r F x z + differencePower r F y z) := by
    apply FracGeometry.ofReal_rpow_le_power_sum (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hr
    simpa only [abs_sub_comm (F z) (F y)] using abs_sub_le (F x) (F z) (F y)
  have h := lintegral_mono (μ := volume.restrict B) hpoint
  rw [lintegral_const, Measure.restrict_apply_univ,
    lintegral_const_mul' _ _ htwo,
    lintegral_add_left (measurable_differencePower r hF x)] at h
  have hcancel := mul_le_mul_left h (volume B)⁻¹
  rw [mul_assoc, ENNReal.mul_inv_cancel hB0 hBtop, mul_one] at hcancel
  have hsub := midpoint_ball_subset hxy
  have hx := lintegral_mono_set (μ := volume) (fun z hz => (hsub hz).1) (f := differencePower r F x)
  have hy := lintegral_mono_set (μ := volume) (fun z hz => (hsub hz).2) (f := differencePower r F y)
  have hinv : (volume B)⁻¹ = ENNReal.ofReal (((d : ℝ) + 1) ^ d) *
      ENNReal.ofReal (ℓ ^ (-(d : ℝ))) := by
    dsimp only [B]
    rw [Real.volume_pi_ball _ hR, Fintype.card_fin,
      ← ENNReal.ofReal_inv_of_pos (pow_pos (by positivity) _),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg hℓ.le, Real.rpow_natCast]
    have hdim : (d : ℝ) + 1 ≠ 0 := by positivity
    have he : 2 * (ℓ / (2 * ((d : ℝ) + 1))) = ℓ / ((d : ℝ) + 1) := by field_simp
    rw [he, div_pow, inv_div, div_eq_mul_inv]
  rw [hinv] at hcancel
  exact hcancel.trans (by
    simpa only [B, ℓ, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_left (add_le_add hx hy)
        (ENNReal.ofReal (((d : ℝ) + 1) ^ d) * ENNReal.ofReal (ℓ ^ (-(d : ℝ))) * (2 : ℝ≥0∞) ^ r))

end

end CoarseDeGiorgi.Foundations.Slicing
