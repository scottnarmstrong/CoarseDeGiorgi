import CoarseDeGiorgi.Foundations.FractionalSobolev.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace CoarseDeGiorgi.Foundations.FractionalSobolev

open Homogenization MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

def setEstimateConstant (n : ℕ) (β : ℝ) : ℝ :=
  (Real.sqrt (n : ℝ)) ^ (-((n : ℝ) + β))

theorem setEstimateConstant_pos {n : ℕ} (hn : 0 < n) (β : ℝ) :
    0 < setEstimateConstant n β :=
  Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hn)) _

theorem set_estimate_at_scale {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β)
    {E : Set (Vec n)} (hE : MeasurableSet E) (x : Vec n) {m : ℝ} (hm : 0 < m)
    (hEm : volume E ≤ ENNReal.ofReal m) :
    ENNReal.ofReal (setEstimateConstant n β) * (ENNReal.ofReal m).rpow (-β / n) ≤
      ∫⁻ y in Eᶜ, ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + β)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let r := m ^ ((n : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hm _
  have hrn : r ^ n = m := Real.rpow_inv_natCast_pow hm.le (ne_of_gt hn)
  let B := Metric.ball x r
  have hB : volume B = ENNReal.ofReal ((2 : ℝ) ^ n * m) := by
    rw [show B = Metric.ball x r from rfl, Real.volume_pi_ball x hr]
    simp only [Fintype.card_fin, mul_pow, hrn]
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hmass : ENNReal.ofReal m ≤ volume (B \ E) := by
    calc
      ENNReal.ofReal m = ENNReal.ofReal (2 * m) - ENNReal.ofReal m := by
        rw [← ENNReal.ofReal_sub _ hm.le]
        congr 1
        ring
      _ ≤ volume B - volume E := by
        apply tsub_le_tsub _ hEm
        rw [hB]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right htwo hm.le)
      _ ≤ volume (B \ E) := le_measure_sdiff
  let c := (Real.sqrt (n : ℝ) * r) ^ (-((n : ℝ) + β))
  have hc : 0 < c := Real.rpow_pos_of_pos (mul_pos (Real.sqrt_pos.mpr hnR) hr) _
  have hpoint : ∀ᵐ y ∂volume.restrict (B \ E),
      ENNReal.ofReal c ≤ ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + β)) := by
    have hne : ∀ᵐ y ∂volume, y ≠ x := by
      simp only [ae_iff, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
    filter_upwards [ae_restrict_of_ae hne,
      ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff hE)] with y hxy hy
    have hd := euclidDist_pos hxy.symm
    have hb := euclidDist_le_of_mem_ball hr hy.1
    apply ENNReal.ofReal_le_ofReal
    change (Real.sqrt (n : ℝ) * r) ^ (-((n : ℝ) + β)) ≤ _
    rw [Real.rpow_neg (mul_nonneg (Real.sqrt_nonneg _) hr.le), ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hd _) 
      (Real.rpow_le_rpow hd.le hb (by linarith only [hnR, hβ]))
  have hint : ENNReal.ofReal c * ENNReal.ofReal m ≤
      ∫⁻ y in Eᶜ, ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + β)) := by
    calc
      ENNReal.ofReal c * ENNReal.ofReal m ≤ ENNReal.ofReal c * volume (B \ E) :=
        mul_le_mul' le_rfl hmass
      _ = ∫⁻ _y in B \ E, ENNReal.ofReal c := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ y in B \ E, ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + β)) :=
        lintegral_mono_ae hpoint
      _ ≤ ∫⁻ y in Eᶜ, ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + β)) :=
        lintegral_mono_set (fun _ hy => hy.2)
  have halgebra : c * m = setEstimateConstant n β * m ^ (-β / n) := by
    dsimp [c, r, setEstimateConstant]
    rw [Real.mul_rpow (Real.sqrt_nonneg _) hr.le, ← Real.rpow_mul hm.le]
    have he : (n : ℝ)⁻¹ * (-((n : ℝ) + β)) + 1 = -β / n := by
      field_simp
      ring
    have hprod : m ^ ((n : ℝ)⁻¹ * (-((n : ℝ) + β))) * m = m ^ (-β / n) := by
      calc
        _ = m ^ ((n : ℝ)⁻¹ * (-((n : ℝ) + β))) * m ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = m ^ (((n : ℝ)⁻¹ * (-((n : ℝ) + β))) + 1) := (Real.rpow_add hm _ _).symm
        _ = m ^ (-β / n) := by rw [he]
    rw [mul_assoc, hprod]
  change ENNReal.ofReal (setEstimateConstant n β) * (ENNReal.ofReal m) ^ (-β / n) ≤ _
  rw [ENNReal.ofReal_rpow_of_pos hm, ← ENNReal.ofReal_mul
    (setEstimateConstant_pos hn β).le, ← halgebra,
    ENNReal.ofReal_mul hc.le]
  exact hint

/-- The explicit constant in DNPV Lemma 6.1, also for measure-zero sets. -/
theorem set_estimate {n : ℕ} (hn : 0 < n) {s p : ℝ} (hs : 0 < s) (hp : 0 < p)
    {E : Set (Vec n)} (hE : MeasurableSet E) (hfin : volume E < ⊤) (x : Vec n) :
    ENNReal.ofReal (setEstimateConstant n (s * p)) * (volume E).rpow (-(s * p) / n) ≤
      ∫⁻ y in Eᶜ, ENNReal.ofReal (1 / euclidDist x y ^ ((n : ℝ) + s * p)) := by
  let m : ℕ → ℝ := fun k => (volume E).toReal + 1 / ((k : ℝ) + 1)
  have hm : ∀ k, 0 < m k := fun k => add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg
    (one_div_pos.mpr (by positivity))
  have hEm : ∀ k, volume E ≤ ENNReal.ofReal (m k) := by
    intro k
    apply (ENNReal.le_ofReal_iff_toReal_le (ne_of_lt hfin) (hm k).le).mpr
    exact le_add_of_nonneg_right (by positivity)
  have hlimit : Tendsto (fun k => ENNReal.ofReal (m k)) atTop (𝓝 (volume E)) := by
    have ht := ENNReal.tendsto_ofReal
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (volume E).toReal)
    simpa only [add_zero, ENNReal.ofReal_toReal (ne_of_lt hfin)] using ht
  have hpow := (ENNReal.continuous_rpow_const (y := -(s * p) / n)).tendsto (volume E)
  have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (setEstimateConstant n (s * p)))
    (hpow.comp hlimit)
    (Or.inr ENNReal.ofReal_ne_top)
  change ENNReal.ofReal (setEstimateConstant n (s * p)) * (volume E) ^ (-(s * p) / n) ≤ _
  exact le_of_tendsto' ht (fun k => set_estimate_at_scale hn (mul_pos hs hp) hE x (hm k) (hEm k))

end

end CoarseDeGiorgi.Foundations.FractionalSobolev
