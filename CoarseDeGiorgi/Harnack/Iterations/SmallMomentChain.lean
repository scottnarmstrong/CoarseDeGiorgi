module

public import CoarseDeGiorgi.Harnack.Iterations.ExponentialCost
public import CoarseDeGiorgi.Harnack.Iterations.MomentNormalization
public import CoarseDeGiorgi.Harnack.Iterations.PowerMomentChain
public import CoarseDeGiorgi.Harnack.Iterations.StoppingExponents
public import CoarseDeGiorgi.Harnack.ReverseMoments.MomentConversion
public import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas
public import Mathlib.Tactic

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- The finite small-moment chain, with its first crossing at one, gives the
all-radii unnormalized estimate. The only input is the powered one-step
moment estimate with a uniform logarithmic gap cost.
-/
theorem small_moment_chain_of_log_step {d : ℕ} {χ A g : ℝ}
    (hχ : 1 < χ) (hA : 0 ≤ A) (hg : 0 ≤ g)
    (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (originCube 1)))
    (hstep : ∀ (a : ℝ) (ha : 0 < a), a < 1 →
      ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
        normalizedLpMoment (χ * a) (mul_pos (zero_lt_one.trans hχ) ha)
          (originCube ρ) f ^ a ≤
        ENNReal.ofReal (Real.exp (A + g * Real.log (1 / (R - ρ)))) *
          normalizedLpMoment a ha (originCube R) f ^ a)
    {b ρ R : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hρ : 1 / 2 ≤ ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    eLpNorm f 1 (volume.restrict (originCube ρ)) ≤
      ENNReal.ofReal (Real.exp
        ((A * (χ / (χ - 1)) + g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2) +
          (g * χ / (χ - 1)) * Real.log (1 / (R - ρ))) / b)) *
        (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ (1 / b) *
          eLpNorm f (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
  have hχpos : 0 < χ := zero_lt_one.trans hχ
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδ1 : R - ρ ≤ 1 := by linarith
  have hρpos : 0 < ρ := by linarith
  have hRpos : 0 < R := hρpos.trans hρR
  let rad : ℕ → ℝ := fun j => ρ + (1 / 2 : ℝ) ^ j * (R - ρ)
  let ex : ℕ → ℝ := fun j => b * χ ^ j
  let L : ℕ → ℝ := fun j => A + g * Real.log (1 / (R - ρ)) +
    g * Real.log 2 * ((j : ℝ) + 1)
  let K : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (L j))
  have hex : ∀ j, 0 < ex j := fun j => mul_pos hb (pow_pos hχpos j)
  have hrad (j : ℕ) : ρ < rad j ∧ rad j ≤ R := by
    have hpos : 0 < (1 / 2 : ℝ) ^ j := by positivity
    have hle : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [rad]
    constructor
    · linarith [mul_pos hpos hδ]
    · nlinarith
  have hgap (j : ℕ) : rad j - rad (j + 1) =
      (1 / 2 : ℝ) ^ (j + 1) * (R - ρ) := by
    dsimp [rad]
    rw [pow_succ]
    ring
  have hloggap (j : ℕ) : Real.log (1 / (rad j - rad (j + 1))) =
      Real.log (1 / (R - ρ)) + ((j : ℝ) + 1) * Real.log 2 := by
    rw [hgap]
    simp only [one_div, Real.log_inv]
    rw [Real.log_mul (by positivity) hδ.ne', Real.log_pow]
    rw [Real.log_inv]
    push_cast
    ring
  obtain ⟨N, _, hcross, _, hbefore⟩ := exists_geometric_first_crossing hχ hb hb1
  let M : ℕ → ℝ≥0∞ := fun j => normalizedLpMoment (ex j) (hex j)
    (originCube (rad j)) f
  have hchainstep : ∀ j < N, M (j + 1) ^ (ex j) ≤ K j * M j ^ (ex j) := by
    intro j hj
    have hnext : rad (j + 1) < rad j := by
      have hp : 0 < (1 / 2 : ℝ) ^ (j + 1) * (R - ρ) := by positivity
      linarith [hgap j]
    have h := hstep (ex j) (hex j) (hbefore j hj)
      (rad (j + 1)) (rad j) (by linarith [(hrad (j + 1)).1]) hnext
      ((hrad j).2.trans hR)
    have hexnext : χ * ex j = ex (j + 1) := by dsimp [ex]; rw [pow_succ]; ring
    simp only [hloggap, hexnext] at h
    have hL : A + g * (Real.log (1 / (R - ρ)) + ((j : ℝ) + 1) * Real.log 2) =
        L j := by dsimp [L]; ring
    simpa only [hL, K, M] using h
  have hchain := finite_rpow_iteration_chain_product M K ex N
    (fun j _ => hex j) hchainstep
  have hlogδ : 0 ≤ Real.log (1 / (R - ρ)) :=
    Real.log_nonneg ((one_le_div hδ).2 hδ1)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hcost := radius_affine_cost_sum_le hχ
    (show 0 ≤ A + g * Real.log (1 / (R - ρ)) by positivity)
    (show 0 ≤ g * Real.log 2 by positivity) N
  have hcost' : (∑ j ∈ Finset.range N, (χ⁻¹) ^ j * L j) ≤
      A * (χ / (χ - 1)) + g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2) +
        (g * χ / (χ - 1)) * Real.log (1 / (R - ρ)) := by
    calc
      _ ≤ (A + g * Real.log (1 / (R - ρ))) * (χ / (χ - 1)) +
          g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2) := hcost
      _ = _ := by ring
  have hprod := geometric_cost_product_le hχpos hb L K N
    (fun _ _ => le_rfl) hcost'
  have hfN := hf.mono_measure (Measure.restrict_mono
    (Scalar.originCube_subset_of_le_one ((hrad N).2.trans hR)) le_rfl)
  have hterminal : eLpNorm f 1 (volume.restrict (originCube ρ)) ≤ M N := by
    exact eLpNorm_one_le_stopped_normalizedMoment (originCube ρ) (originCube (rad N))
      f hcross (Scalar.originCube_subset_of_le (hrad N).1.le) hfN
      (Scalar.volume_originCube_le_one (by linarith))
      (Scalar.volume_originCube_pos (hρpos.trans (hrad N).1))
      (Scalar.volume_originCube_le_one ((hrad N).2.trans hR))
  have hfR := hf.mono_measure (Measure.restrict_mono
    (Scalar.originCube_subset_of_le_one hR) le_rfl)
  have hinv : (volume (originCube (d := d) R))⁻¹ ≤ ENNReal.ofReal ((2 : ℝ) ^ d) := by
    rw [ReverseMoments.originCube_volume R hRpos.le,
      ← ENNReal.ofReal_inv_of_pos (pow_pos hRpos d)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : (1 / 2 : ℝ) ^ d ≤ R ^ d := by gcongr; linarith
    have h := one_div_le_one_div_of_le (by positivity : 0 < (1 / 2 : ℝ) ^ d) hpow
    simpa only [one_div, inv_pow, inv_div, one_mul, inv_inv] using h
  have houter : M 0 ≤ (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ (1 / b) *
      eLpNorm f (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
    dsimp [M, ex, rad]
    simp only [pow_zero, mul_one, one_mul, add_sub_cancel]
    rw [normalizedLpMoment_eq_eLpNorm (originCube R) f hb hfR,
      ENNReal.rpow_neg, ← ENNReal.inv_rpow]
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hinv (by positivity)) zero_le
  calc
    _ ≤ M N := hterminal
    _ ≤ (∏ j ∈ Finset.range N, K j ^ (1 / ex j)) * M 0 := hchain
    _ ≤ ENNReal.ofReal (Real.exp
        ((A * (χ / (χ - 1)) + g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2) +
          (g * χ / (χ - 1)) * Real.log (1 / (R - ρ))) / b)) * M 0 := by
      exact mul_le_mul_of_nonneg_right hprod zero_le
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left houter
        (show 0 ≤ ENNReal.ofReal (Real.exp
          ((A * (χ / (χ - 1)) + g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2) +
            (g * χ / (χ - 1)) * Real.log (1 / (R - ρ))) / b)) from zero_le)
      simpa only [mul_assoc] using h

/-- The small chain has the literal all-radii gap factor consumed by crossover.
-/
theorem small_moment_iteration_of_log_step {d : ℕ} {χ A g : ℝ}
    (hχ : 1 < χ) (hA : 0 ≤ A) (hg : 0 ≤ g)
    (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (originCube 1)))
    (hstep : ∀ (a : ℝ) (ha : 0 < a), a < 1 →
      ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
        normalizedLpMoment (χ * a) (mul_pos (zero_lt_one.trans hχ) ha)
          (originCube ρ) f ^ a ≤
        ENNReal.ofReal (Real.exp (A + g * Real.log (1 / (R - ρ)))) *
          normalizedLpMoment a ha (originCube R) f ^ a)
    {b ρ R : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hρ : 1 / 2 ≤ ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    let C₃ := Real.exp (A * (χ / (χ - 1)) +
      g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2))
    let γ₆ := g * χ / (χ - 1)
    eLpNorm f 1 (volume.restrict (originCube ρ)) ≤
      (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
        eLpNorm f (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
  have h := small_moment_chain_of_log_step hχ hA hg f hf hstep hb hb1 hρ hρR hR
  rw [mul_assoc] at h
  rw [← mul_assoc] at h
  rw [exponential_gap_factor_identity (sub_pos.mpr hρR) hb
    (by positivity : 0 < (2 : ℝ) ^ d)] at h
  exact h

end CoarseDeGiorgi.Harnack.Iterations
