import CoarseDeGiorgi.Harnack.Iterations.GeometricEndpoints
import CoarseDeGiorgi.Harnack.Iterations.EndpointGeometry
import CoarseDeGiorgi.Harnack.Iterations.StoppingExponents

open Homogenization MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi.Harnack.Iterations

/-- The infinite reciprocal and stopped positive chains share one logarithmic
constant. The input is their geometric one-step estimate on arbitrary radii.
-/
theorem endpoint_iterations_of_geometric_steps {d : ℕ} {χ A g β b η : ℝ}
    (hχ : 1 < χ) (hA : 0 ≤ A) (hg : 0 ≤ g) (hβ : 0 ≤ β)
    (hb : 0 < b) (hη : 0 < η) (hbη : b < η)
    (U : Vec d → ℝ)
    (hU : AEStronglyMeasurable U (volume.restrict (originCube 1)))
    (hUpos : ∀ᵐ x ∂volume.restrict (originCube 1), 0 < U x)
    (hnegative : ∀ j : ℕ, ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
      normalizedLpMoment (b * χ ^ (j + 1)) (by positivity)
        (originCube ρ) (fun x => (U x)⁻¹) ^ (b * χ ^ j) ≤
        ENNReal.ofReal (Real.exp (A + g * Real.log (1 / (R - ρ)) +
          2 * β * (j : ℝ) * Real.log χ)) *
          normalizedLpMoment (b * χ ^ j) (by positivity)
            (originCube R) (fun x => (U x)⁻¹) ^ (b * χ ^ j))
    (hpositive : ∀ j : ℕ, b * χ ^ j < η →
      ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
      normalizedLpMoment (b * χ ^ (j + 1)) (by positivity)
        (originCube ρ) U ^ (b * χ ^ j) ≤
        ENNReal.ofReal (Real.exp (A + g * Real.log (1 / (R - ρ)) +
          2 * β * (j : ℝ) * Real.log χ)) *
          normalizedLpMoment (b * χ ^ j) (by positivity)
            (originCube R) U ^ (b * χ ^ j))
    {ρ R : ℝ} (hρ : 1 / 2 ≤ ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    let B := A * (χ / (χ - 1)) +
      (g * Real.log 2 + 2 * β * Real.log χ) * (χ ^ 2 / (χ - 1) ^ 2)
    let γ₆ := g * χ / (χ - 1)
    let H := (ENNReal.ofReal (((2 : ℝ) ^ d * Real.exp B) *
      (R - ρ) ^ (-γ₆))) ^ (1 / b)
    (H * normalizedLpMoment b hb (originCube R) (fun x => (U x)⁻¹))⁻¹ ≤
      nonnegativeEssInf (originCube ρ) U ∧
    normalizedLpMoment η hη (originCube ρ) U ≤
      H * normalizedLpMoment b hb (originCube R) U := by
  let B := A * (χ / (χ - 1)) +
    (g * Real.log 2 + 2 * β * Real.log χ) * (χ ^ 2 / (χ - 1) ^ 2)
  let γ₆ := g * χ / (χ - 1)
  let rad := fun j : ℕ => ρ + (1 / 2 : ℝ) ^ j * (R - ρ)
  let V := fun j : ℕ => originCube (d := d) (rad j)
  let L := fun j : ℕ => A + g * Real.log (1 / (R - ρ)) +
    g * Real.log 2 * ((j : ℝ) + 1) + 2 * β * (j : ℝ) * Real.log χ
  let T := ENNReal.ofReal (Real.exp ((B + γ₆ * Real.log (1 / (R - ρ))) / b))
  let D := ENNReal.ofReal ((2 : ℝ) ^ d)
  have hχpos := zero_lt_one.trans hχ
  have hδ := sub_pos.mpr hρR
  have hρpos : 0 < ρ := by linarith
  have hrad := iteration_radius_bounds hρR
  have hradnext (j : ℕ) : rad (j + 1) < rad j := by
    dsimp [rad]
    rw [pow_succ]
    have hpow : 0 < (1 / 2 : ℝ) ^ j * (R - ρ) := by positivity
    linarith
  have hcost (n : ℕ) : (∑ j ∈ Finset.range n, (χ⁻¹) ^ j * L j) ≤
      B + γ₆ * Real.log (1 / (R - ρ)) := by
    have hlogδ : 0 ≤ Real.log (1 / (R - ρ)) :=
      Real.log_nonneg ((one_le_div hδ).2 (by linarith))
    have hlog2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have hlogχ := Real.log_nonneg hχ.le
    have h := radius_affine_cost_sum_le hχ
      (show 0 ≤ A + g * Real.log (1 / (R - ρ)) by positivity)
      (show 0 ≤ g * Real.log 2 + 2 * β * Real.log χ by positivity) n
    have hterm (j : ℕ) : L j ≤
        (A + g * Real.log (1 / (R - ρ))) +
          (g * Real.log 2 + 2 * β * Real.log χ) * ((j : ℝ) + 1) := by
      dsimp [L]
      nlinarith [mul_nonneg hβ hlogχ]
    calc
      _ ≤ ∑ j ∈ Finset.range n, (χ⁻¹) ^ j *
          ((A + g * Real.log (1 / (R - ρ))) +
            (g * Real.log 2 + 2 * β * Real.log χ) * ((j : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hterm j) (by positivity)
      _ ≤ _ := by dsimp [B, γ₆]; convert h using 1; ring
  have hnegstep (j : ℕ) : normalizedLpMoment (b * χ ^ (j + 1)) (by positivity)
      (V (j + 1)) (fun x => (U x)⁻¹) ^ (b * χ ^ j) ≤
        ENNReal.ofReal (Real.exp (L j)) * normalizedLpMoment (b * χ ^ j)
          (by positivity) (V j) (fun x => (U x)⁻¹) ^ (b * χ ^ j) := by
    have h := hnegative j (rad (j + 1)) (rad j)
      (by linarith [(hrad (j + 1)).1]) (hradnext j) ((hrad j).2.trans hR)
    rw [iteration_radius_log_gap hρR j] at h
    simpa only [V, L, rad, mul_add, mul_assoc, add_assoc, mul_comm, mul_left_comm] using h
  have hinvmeas := hU.aemeasurable.inv.aestronglyMeasurable
  have hmeas (j : ℕ) : AEStronglyMeasurable (fun x => (U x)⁻¹)
      (volume.restrict (V j)) := hinvmeas.mono_measure
    (Measure.restrict_mono (Scalar.originCube_subset_of_le_one ((hrad j).2.trans hR)) le_rfl)
  have hEtop : volume (originCube (d := d) ρ) < ⊤ := (Scalar.volume_originCube_le_one (by linarith : ρ ≤ 1)).trans_lt ENNReal.one_lt_top
  have hDpos : 0 < D := ENNReal.ofReal_pos.mpr (by positivity)
  have hDtop : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnegbound := geometric_reciprocal_chain_essential_bound (originCube ρ) V U
    hχ hb L (Scalar.volume_originCube_pos hρpos) hEtop.ne hDpos hDtop
    (fun j => Scalar.originCube_subset_of_le (hrad j).1.le)
    (fun j => iteration_cube_volume_le hρ ((hrad j).2.trans hR))
    (ae_restrict_of_ae_restrict_of_subset (Scalar.originCube_subset_of_le_one (by linarith)) hUpos)
    hmeas hnegstep hcost
  have hD1 : 1 ≤ D := by
    simpa [D] using ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hH : T * D ^ (1 / b) =
      (ENNReal.ofReal (((2 : ℝ) ^ d * Real.exp B) * (R - ρ) ^ (-γ₆))) ^ (1 / b) :=
    exponential_gap_factor_identity hδ hb (by positivity)
  have hTle : T ≤ T * D ^ (1 / b) := by
    calc
      _ = T * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (ENNReal.one_le_rpow hD1 (by positivity)) zero_le
  constructor
  · apply le_trans _ hnegbound
    apply ENNReal.inv_le_inv.mpr
    simpa only [V, rad, pow_zero, one_mul, add_sub_cancel, hH] using
      mul_le_mul_of_nonneg_right hTle zero_le
  · obtain ⟨N, _, hcross, _, hbefore⟩ := exists_geometric_first_crossing hχ hb hbη
    have hposstep (j : ℕ) (hj : j < N) :
        normalizedLpMoment (b * χ ^ (j + 1)) (by positivity) (V (j + 1)) U ^ (b * χ ^ j) ≤
          ENNReal.ofReal (Real.exp (L j)) *
            normalizedLpMoment (b * χ ^ j) (by positivity) (V j) U ^ (b * χ ^ j) := by
      have h := hpositive j (hbefore j hj) (rad (j + 1)) (rad j)
        (by linarith [(hrad (j + 1)).1]) (hradnext j) ((hrad j).2.trans hR)
      rw [iteration_radius_log_gap hρR j] at h
      simpa only [V, L, rad, mul_add, mul_assoc, add_assoc, mul_comm, mul_left_comm] using h
    have h := geometric_stopped_chain_subset_bound (originCube ρ) V U hχpos hb hη
      L N hcross hposstep (hcost N) (Scalar.originCube_subset_of_le (hrad N).1.le)
      (hU.mono_measure (Measure.restrict_mono
        (Scalar.originCube_subset_of_le_one ((hrad N).2.trans hR)) le_rfl))
      (Scalar.volume_originCube_pos hρpos) hEtop.ne
      (Scalar.volume_originCube_pos (hρpos.trans (hrad N).1))
      (((Scalar.volume_originCube_le_one ((hrad N).2.trans hR)).trans_lt ENNReal.one_lt_top).ne)
    have hex : b ≤ b * χ ^ N := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hχ.le) hb.le
    have hfactor := iteration_cube_subset_factor_le (d := d) hρ ((hrad N).2.trans hR) hb hex
    have h' := h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfactor zero_le) zero_le)
    rw [mul_comm (D ^ (1 / b)) T, hH] at h'
    simpa only [V, rad, pow_zero, mul_one, one_mul, add_sub_cancel] using h'

end CoarseDeGiorgi.Harnack.Iterations
