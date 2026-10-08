import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Uniform dyadic tail estimates for the integrated slicing argument. -/

open MeasureTheory Set
open scoped ENNReal

namespace CoarseDeGiorgi.Foundations.Slicing

/-- Positive extra decay can be discarded uniformly in the dyadic sum. -/
theorem dyadic_decay_le {d γ : ℝ} (hd : 1 ≤ d) (hγ : 0 ≤ γ) (j : ℕ) :
    (2 : ℝ) ^ (-(j : ℝ) * (d + γ)) ≤ (1 / 2 : ℝ) ^ j := by
  calc
    _ ≤ (2 : ℝ) ^ (-(j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith only [hd, hγ, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    _ = _ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
        ← inv_pow, inv_eq_one_div]

/-- The annular decay sum is at most two, independently of the extra exponent. -/
theorem tsum_dyadic_decay_le {d γ : ℝ} (hd : 1 ≤ d) (hγ : 0 ≤ γ) :
    (∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ) * (d + γ)))) ≤ 2 := by
  calc
    _ ≤ ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j := by
      apply ENNReal.tsum_le_tsum
      intro j
      have h := ENNReal.ofReal_le_ofReal (dyadic_decay_le hd hγ j)
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at h
      norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div] at h
      exact h
    _ = 2 := ENNReal.tsum_geometric_two

private theorem annular_coefficient {m q R : ℝ} (hR : 0 < R) (j : ℕ) :
    ((2 : ℝ) ^ j * R) ^ (-q) * ((2 : ℝ) ^ (j + 1) * R) ^ m =
      (2 : ℝ) ^ m * R ^ (m - q) * (2 : ℝ) ^ ((j : ℝ) * (m - q)) := by
  rw [Real.mul_rpow (by positivity) hR.le,
    Real.mul_rpow (by positivity) hR.le,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show m - q = m + -q by ring, Real.rpow_add hR]
  rw [show (j : ℝ) * (m + -q) = (j : ℝ) * m + (j : ℝ) * -q by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show ((j + 1 : ℕ) : ℝ) * m = m + (j : ℝ) * m by push_cast; ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring

/-- A polynomial ball-growth bound controls the exterior inverse-power kernel.
The coefficient is uniform in every `q ≥ m + 1`, including the slicing exponent
`q = 2d - 1 + α ξ`, `m = d - 1`. -/
theorem lintegral_tail_le_of_growth {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {g : X → ℝ} (hg : Measurable g)
    {K m q R : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hq : m + 1 ≤ q) (hR : 0 < R)
    (hgrowth : ∀ T : ℝ, 0 < T →
      μ {x | g x < T} ≤ ENNReal.ofReal (K * T ^ m)) :
    (∫⁻ x in {x | R < g x}, ENNReal.ofReal ((g x) ^ (-q)) ∂μ) ≤
      ENNReal.ofReal (2 * K * (2 : ℝ) ^ m * R ^ (m - q)) := by
  classical
  let A : ℕ → Set X := fun j => {x | g x < (2 : ℝ) ^ (j + 1) * R}
  let c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (((2 : ℝ) ^ j * R) ^ (-q))
  have hA (j : ℕ) : MeasurableSet (A j) := measurableSet_lt hg measurable_const
  have hq0 : 0 ≤ q := by linarith only [hm, hq]
  have hmajor : ∀ x : X,
      {x | R < g x}.indicator (fun x => ENNReal.ofReal ((g x) ^ (-q))) x ≤
        ∑' j : ℕ, (A j).indicator (fun _ => c j) x := by
    intro x
    by_cases hx : R < g x
    · rw [indicator_of_mem (show x ∈ {x | R < g x} from hx)]
      have hratio : 1 ≤ g x / R := (le_div_iff₀ hR).mpr (by simpa using hx.le)
      obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
      have hlo : (2 : ℝ) ^ j * R ≤ g x := (le_div_iff₀ hR).mp hjlo
      have hhi : x ∈ A j := (div_lt_iff₀ hR).mp hjhi
      have hpow := Real.rpow_le_rpow_of_nonpos
        (by positivity : 0 < (2 : ℝ) ^ j * R) hlo (neg_nonpos.mpr hq0)
      calc
        _ ≤ c j := ENNReal.ofReal_le_ofReal hpow
        _ = (A j).indicator (fun _ => c j) x := (indicator_of_mem hhi (fun _ : X => c j)).symm
        _ ≤ _ := ENNReal.le_tsum (f := fun k : ℕ => (A k).indicator (fun _ => c k) x) j
    · rw [indicator_of_notMem (show x ∉ {x | R < g x} from hx)]
      exact bot_le
  rw [← lintegral_indicator (measurableSet_lt measurable_const hg)]
  calc
    _ ≤ ∫⁻ x, ∑' j : ℕ, (A j).indicator (fun _ => c j) x ∂μ := lintegral_mono hmajor
    _ = ∑' j : ℕ, c j * μ (A j) := by
      rw [lintegral_tsum (fun j => (measurable_const.indicator (hA j)).aemeasurable)]
      simp_rw [lintegral_indicator_const (hA _)]
    _ ≤ ∑' j : ℕ, c j * ENNReal.ofReal (K * ((2 : ℝ) ^ (j + 1) * R) ^ m) := by
      apply ENNReal.tsum_le_tsum
      intro j
      exact mul_le_mul_right (hgrowth ((2 : ℝ) ^ (j + 1) * R)
        (mul_pos (pow_pos (by norm_num) _) hR)) (c j)
    _ = ENNReal.ofReal (K * (2 : ℝ) ^ m * R ^ (m - q)) *
        ∑' j : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ) * (q - m))) := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext j
      dsimp only [c]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_left_comm _ K, annular_coefficient hR j]
      rw [show -(j : ℝ) * (q - m) = (j : ℝ) * (m - q) by ring]
      ring
    _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ m * R ^ (m - q)) * 2 := by
      apply mul_le_mul_right
      simpa only [add_zero] using tsum_dyadic_decay_le (d := q - m) (γ := 0)
        (by linarith only [hq]) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end CoarseDeGiorgi.Foundations.Slicing
