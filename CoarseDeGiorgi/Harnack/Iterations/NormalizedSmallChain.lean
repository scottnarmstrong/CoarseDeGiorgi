import CoarseDeGiorgi.Harnack.Iterations.SmallMomentChain
import CoarseDeGiorgi.Harnack.Iterations.EndpointGeometry
import CoarseDeGiorgi.Harnack.Iterations.PositiveMomentStop

open Homogenization MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi.Harnack.Iterations

/-- The full normalized small-moment family, including every 0<a<b≤1.
-/
theorem normalized_small_moment_chain_of_log_step {d : ℕ} {χ A g : ℝ}
    (hχ : 1 < χ) (hA : 0 ≤ A) (hg : 0 ≤ g)
    (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (originCube 1)))
    (hstep : ∀ (a : ℝ) (ha : 0 < a), a < 1 →
      ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
        normalizedLpMoment (χ * a) (mul_pos (zero_lt_one.trans hχ) ha)
          (originCube ρ) f ^ a ≤
        ENNReal.ofReal (Real.exp (A + g * Real.log (1 / (R - ρ)))) *
          normalizedLpMoment a ha (originCube R) f ^ a)
    {a b ρ R : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    (hρ : 1 / 2 ≤ ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    let C₃ := (2 : ℝ) ^ d * Real.exp
      (A * (χ / (χ - 1)) + g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2))
    let γ₆ := g * χ / (χ - 1)
    normalizedLpMoment b (ha.trans hab) (originCube ρ) f ≤
      (ENNReal.ofReal (C₃ * (R - ρ) ^ (-γ₆))) ^ (1 / a) *
        normalizedLpMoment a ha (originCube R) f
 := by
  have hχpos : 0 < χ := zero_lt_one.trans hχ
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδ1 : R - ρ ≤ 1 := by linarith
  have hρpos : 0 < ρ := by linarith
  have hRpos : 0 < R := hρpos.trans hρR
  let rad : ℕ → ℝ := fun j => ρ + (1 / 2 : ℝ) ^ j * (R - ρ)
  let ex : ℕ → ℝ := fun j => a * χ ^ j
  let L : ℕ → ℝ := fun j => A + g * Real.log (1 / (R - ρ)) +
    g * Real.log 2 * ((j : ℝ) + 1)
  let K : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (L j))
  have hex : ∀ j, 0 < ex j := fun j => mul_pos ha (pow_pos hχpos j)
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
  obtain ⟨N, _, hcross, _, hbefore⟩ := exists_geometric_first_crossing hχ ha hab
  let M : ℕ → ℝ≥0∞ := fun j => normalizedLpMoment (ex j) (hex j)
    (originCube (rad j)) f
  have hchainstep : ∀ j < N, M (j + 1) ^ (ex j) ≤ K j * M j ^ (ex j) := by
    intro j hj
    have hnext : rad (j + 1) < rad j := by
      have hp : 0 < (1 / 2 : ℝ) ^ (j + 1) * (R - ρ) := by positivity
      linarith [hgap j]
    have h := hstep (ex j) (hex j) ((lt_of_lt_of_le (hbefore j hj) hb1))
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
  have hprod := geometric_cost_product_le hχpos ha L K N
    (fun _ _ => le_rfl) hcost'
  have hfN := hf.mono_measure (Measure.restrict_mono
    (Scalar.originCube_subset_of_le_one ((hrad N).2.trans hR)) le_rfl)
  have hEtop : volume (originCube (d := d) ρ) ≠ ⊤ :=
    ((Scalar.volume_originCube_le_one (hρR.le.trans hR)).trans_lt ENNReal.one_lt_top).ne
  have hNtop : volume (originCube (d := d) (rad N)) ≠ ⊤ :=
    ((Scalar.volume_originCube_le_one ((hrad N).2.trans hR)).trans_lt ENNReal.one_lt_top).ne
  have htransfer := normalizedLpMoment_subset_bound (originCube ρ) (originCube (rad N)) f
    (ha.trans hab) (hex N) hcross (Scalar.originCube_subset_of_le (hrad N).1.le)
    hfN (Scalar.volume_originCube_pos hρpos) hEtop
    (Scalar.volume_originCube_pos (hρpos.trans (hrad N).1)) hNtop
  have hexle : a ≤ ex N := by
    simpa [ex] using mul_le_mul_of_nonneg_left (one_le_pow₀ hχ.le (n := N)) ha.le
  have hfactor := iteration_cube_subset_factor_le (d := d) hρ ((hrad N).2.trans hR) ha hexle
  let T := ENNReal.ofReal (Real.exp
    ((A * (χ / (χ - 1)) + g * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2) +
      (g * χ / (χ - 1)) * Real.log (1 / (R - ρ))) / a))
  let D := ENNReal.ofReal ((2 : ℝ) ^ d)
  have hbound : normalizedLpMoment b (ha.trans hab) (originCube ρ) f ≤
      (T * D ^ (1 / a)) * M 0 := by
    calc
      _ ≤ (volume (originCube ρ) ^ (-(1 / ex N)) *
          volume (originCube (rad N)) ^ (1 / ex N)) * M N := htransfer
      _ ≤ D ^ (1 / a) * M N := mul_le_mul_of_nonneg_right hfactor zero_le
      _ ≤ D ^ (1 / a) * ((∏ j ∈ Finset.range N, K j ^ (1 / ex j)) * M 0) :=
        mul_le_mul_of_nonneg_left hchain zero_le
      _ ≤ D ^ (1 / a) * (T * M 0) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod zero_le) zero_le
      _ = _ := by ac_rfl
  rw [exponential_gap_factor_identity hδ ha (by positivity : 0 < (2 : ℝ) ^ d)] at hbound
  simpa only [M, ex, rad, pow_zero, mul_one, one_mul, add_sub_cancel] using hbound

end CoarseDeGiorgi.Harnack.Iterations
