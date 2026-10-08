import CoarseDeGiorgi.Harnack.Iterations.MomentPower
import CoarseDeGiorgi.Statements.PowerFactor
import Mathlib.Tactic

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Scale a powered moment step to the moments of a fixed positive power.
-/
theorem normalizedLpMoment_power_step {d : ℕ} (V W : Set (Vec d))
    (hV : MeasurableSet V) (hW : MeasurableSet W) (f : Vec d → ℝ)
    {χ p a : ℝ} (hχ : 0 < χ) (hp : 0 < p) (ha : 0 < a)
    (hfV : ∀ᵐ x ∂volume.restrict V, 0 < f x)
    (hfW : ∀ᵐ x ∂volume.restrict W, 0 < f x)
    (K : ℝ≥0∞)
    (hstep : normalizedLpMoment (χ * (p * a)) (by positivity) V f ^ (p * a) ≤
      K * normalizedLpMoment (p * a) (mul_pos hp ha) W f ^ (p * a)) :
    normalizedLpMoment (χ * a) (mul_pos hχ ha) V (fun x => (f x) ^ p) ^ a ≤
      K * normalizedLpMoment a ha W (fun x => (f x) ^ p) ^ a := by
  have hv := normalizedLpMoment_rpow_scale V hV f (mul_pos hχ ha) hp hfV
  have hw := normalizedLpMoment_rpow_scale W hW f ha hp hfW
  have heq : (χ * a) * p = χ * (p * a) := by ring
  have heq' : a * p = p * a := mul_comm _ _
  simp only [heq, heq'] at hv hw
  change normalizedLpMoment (χ * a) (mul_pos hχ ha) V
      (fun x => Real.rpow (f x) p) ^ a ≤
    K * normalizedLpMoment a ha W (fun x => Real.rpow (f x) p) ^ a
  rw [hv, hw, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  exact hstep

/-- The source factor at `m=z/r` is the squared source denominator ratio.
-/
theorem powerFactor_scaled_sq {z r : ℝ} (hr : 0 < r) (hz : z < r / 2) :
    powerFactor (z / r) ^ 2 = z ^ 2 / (r - 2 * z) ^ 2 := by
  have hden : r - 2 * z ≠ 0 := by linarith
  have hden' : 1 - 2 * (z / r) ≠ 0 := by
    have h : 1 - 2 * (z / r) = (r - 2 * z) / r := by field_simp
    rw [h]
    exact div_ne_zero hden hr.ne'
  unfold powerFactor
  rw [div_pow, sq_abs, div_pow]
  field_simp

/-- Both small signed branches have contrast factor at most one, using only the
crossover exponent bounds already proved from the moment comparison.
-/
theorem small_signed_powerFactor_bound {p c r Θ a z : ℝ}
    (hp : 0 < p) (hpquarter : p < r / 4) (hc : 0 ≤ c)
    (hr : 0 < r) (_hΘ : 0 ≤ Θ) (hpΘ : p ^ 2 * Θ ≤ c ^ 2)
    (hcsmall : 2 * c < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hz : z = p * a ∨ z = -(p * a)) :
    z < r / 2 ∧ powerFactor (z / r) ^ 2 * Θ ≤ 1 := by
  have hpa : 0 < p * a := mul_pos hp ha
  have hpale : p * a ≤ p := by simpa using mul_le_mul_of_nonneg_left ha1 hp.le
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have hnum : (p * a) ^ 2 * Θ ≤ c ^ 2 := by
    calc
      _ = (p ^ 2 * Θ) * a ^ 2 := by ring
      _ ≤ c ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_right hpΘ (sq_nonneg a)
      _ ≤ c ^ 2 := mul_le_of_le_one_right (sq_nonneg c) ha2
  have hzhalf : z < r / 2 := by rcases hz with rfl | rfl <;> linarith
  have hden : r / 2 ≤ r - 2 * z := by rcases hz with rfl | rfl <;> linarith
  have hdenpos : 0 < r - 2 * z := by linarith
  have hzsq : z ^ 2 * Θ ≤ c ^ 2 := by rcases hz with rfl | rfl <;> simpa using hnum
  have hdenSq : (r / 2) ^ 2 ≤ (r - 2 * z) ^ 2 :=
    (sq_le_sq₀ (by positivity) hdenpos.le).2 hden
  refine ⟨hzhalf, ?_⟩
  rw [powerFactor_scaled_sq hr hzhalf]
  have heq : z ^ 2 / (r - 2 * z) ^ 2 * Θ =
      z ^ 2 * Θ / (r - 2 * z) ^ 2 := by ring
  rw [heq, div_le_one (sq_pos_of_pos hdenpos)]
  have hcsq : c ^ 2 ≤ (r / 2) ^ 2 := by nlinarith
  exact hzsq.trans (hcsq.trans hdenSq)

/-- A finite uniform reverse-moment constant and the bounded small-branch
contrast factor give a logarithmic one-step gap cost.
-/
theorem small_reverse_cost_le_exp {C Θ : ℝ≥0∞} {δ γ r β m : ℝ}
    (hC : 1 ≤ C) (hCtop : C < ⊤) (hΘtop : Θ < ⊤)
    (hδ : 0 < δ) (_hr : 0 < r) (hβ : 0 ≤ β)
    (hfactor : powerFactor m ^ 2 * Θ.toReal ≤ 1) :
    C * (ENNReal.ofReal ((δ / 2) ^ (-γ))) ^ r *
      (1 + ENNReal.ofReal (powerFactor m ^ 2) * Θ) ^ β ≤
    ENNReal.ofReal (Real.exp (Real.log C.toReal +
      (γ * r + β) * Real.log 2 + γ * r * Real.log (1 / δ))) := by
  have hCReal : 1 ≤ C.toReal := by
    simpa using ENNReal.toReal_mono hCtop.ne hC
  have hCRealPos : 0 < C.toReal := zero_lt_one.trans_le hCReal
  have hx : ENNReal.ofReal (powerFactor m ^ 2) * Θ ≤ 1 := by
    calc
      _ = ENNReal.ofReal (powerFactor m ^ 2 * Θ.toReal) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_toReal hΘtop.ne]
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hfactor
      _ = 1 := ENNReal.ofReal_one
  have hx2 : 1 + ENNReal.ofReal (powerFactor m ^ 2) * Θ ≤ (2 : ℝ≥0∞) := by
    calc
      _ ≤ 1 + 1 := add_le_add le_rfl hx
      _ = 2 := by norm_num
  have hhalf : 0 < δ / 2 := by positivity
  calc
    _ ≤ C * (ENNReal.ofReal ((δ / 2) ^ (-γ))) ^ r * (2 : ℝ≥0∞) ^ β :=
      mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hx2 hβ) zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_toReal hCtop.ne,
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hhalf _)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C.toReal),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ C.toReal * ((δ / 2) ^ (-γ)) ^ r)]
      congr 1
      rw [Real.rpow_def_of_pos hhalf, ← Real.exp_mul,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        ← Real.exp_log hCRealPos, ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [Real.log_div hδ.ne' (by norm_num : (2 : ℝ) ≠ 0), one_div, Real.log_inv]
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
      ring

end CoarseDeGiorgi.Harnack.Iterations
