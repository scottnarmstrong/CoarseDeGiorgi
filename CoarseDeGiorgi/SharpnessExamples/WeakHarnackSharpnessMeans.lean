module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessCore
public import CoarseDeGiorgi.Statements.NormalizedLpMoment

/-! # The `L^η` mean of the supersolution over `(5/8)□₀` -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem volume_originCube_five_eighths {d : ℕ} [NeZero d] :
    volume (originCube (d := d) (5 / 8)) = ENNReal.ofReal ((5 / 8) ^ d) := by
  rw [originCube_eq_ball_of_pos (by norm_num), Real.volume_pi_ball _ (by norm_num)]
  simp only [Fintype.card_fin]
  norm_num

theorem whMoment_lower {d : ℕ} [NeZero d] (hd : 3 ≤ d) (q t : ℝ) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : G ≤ whU d q t ε (4 * ε ^ 2)) :
    ENNReal.ofReal ((((5 / 8 : ℝ) ^ d)⁻¹ * G ^ η * (4 * ε / whR d) ^ d) ^ (1 / η)) ≤
      normalizedLpMoment η hη (originCube (d := d) (5 / 8)) (whu d q t ε) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := by omega
  have hRpos := whR_pos hd1
  have hR3 : (1 : ℝ) ≤ whR d := by
    unfold whR; rw [Real.one_le_sqrt]; exact_mod_cast hd1
  have hr0 : 0 < 2 * ε / whR d := by positivity
  set B : Set (Vec d) := Metric.ball (0 : Vec d) (2 * ε / whR d) with hB
  have hBV : B ⊆ originCube (d := d) (5 / 8) := by
    rw [originCube_eq_ball_of_pos (by norm_num)]
    apply Metric.ball_subset_ball
    have : 2 * ε / whR d ≤ 2 * ε := by
      rw [div_le_iff₀ hRpos]; nlinarith
    linarith
  have hvolB : volume B = ENNReal.ofReal ((4 * ε / whR d) ^ d) := by
    rw [hB, Real.volume_pi_ball _ hr0]
    simp only [Fintype.card_fin]
    congr 1
    congr 1
    ring
  have hval : ∀ x ∈ B, G ≤ whu d q t ε x := by
    intro x hx
    rw [hB, mem_ball_zero_iff] at hx
    have hσ : vecNormSq x ≤ 4 * ε ^ 2 := by
      have h1 := vecNormSq_le x
      have h2 : ‖x‖ ^ 2 ≤ (2 * ε / whR d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx.le 2
      have h3 : (2 * ε / whR d) ^ 2 * (d : ℝ) = 4 * ε ^ 2 := by
        rw [div_pow, mul_pow, whR_sq]
        field_simp
        norm_num
      nlinarith
    refine hG.trans ?_
    unfold whu
    exact whU_antitone hd1 q t hε hσ (by nlinarith [pow_pos hε 2])
  have hmeasB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  unfold normalizedLpMoment
  have hpos : (0 : ℝ) < ((5 / 8 : ℝ) ^ d) := by positivity
  have hb0 : 0 ≤ (4 * ε / whR d) ^ d := by positivity
  have hg0 : 0 ≤ G ^ η := Real.rpow_nonneg hG0 _
  have hinner : ∫⁻ x in B, (ENNReal.ofReal G).rpow η ≤
      ∫⁻ x in originCube (d := d) (5 / 8), (ENNReal.ofReal |whu d q t ε x|).rpow η := by
    calc ∫⁻ x in B, (ENNReal.ofReal G).rpow η
        ≤ ∫⁻ x in B, (ENNReal.ofReal |whu d q t ε x|).rpow η := by
          apply setLIntegral_mono' hmeasB
          intro x hx
          apply ENNReal.rpow_le_rpow _ hη.le
          exact ENNReal.ofReal_le_ofReal ((hval x hx).trans (le_abs_self _))
      _ ≤ _ := lintegral_mono_set hBV
  have hconst : ∫⁻ x in B, (ENNReal.ofReal G).rpow η = (ENNReal.ofReal G).rpow η * volume B :=
    setLIntegral_const _ _
  rw [hconst] at hinner
  rw [volume_originCube_five_eighths]
  have h1 : (ENNReal.ofReal G).rpow η = ENNReal.ofReal (G ^ η) :=
    ENNReal.ofReal_rpow_of_nonneg hG0 hη.le
  have h2 : (ENNReal.ofReal ((5 / 8 : ℝ) ^ d))⁻¹ = ENNReal.ofReal (((5 / 8 : ℝ) ^ d)⁻¹) :=
    (ENNReal.ofReal_inv_of_pos hpos).symm
  have hr : (0 : ℝ) ≤ 1 / η := by positivity
  calc ENNReal.ofReal ((((5 / 8 : ℝ) ^ d)⁻¹ * G ^ η * (4 * ε / whR d) ^ d) ^ (1 / η))
      = (ENNReal.ofReal (((5 / 8 : ℝ) ^ d)⁻¹ * G ^ η * (4 * ε / whR d) ^ d)).rpow (1 / η) :=
        (ENNReal.ofReal_rpow_of_nonneg (by positivity) hr).symm
    _ = ((ENNReal.ofReal ((5 / 8 : ℝ) ^ d))⁻¹ * ((ENNReal.ofReal G).rpow η * volume B)).rpow
          (1 / η) := by
        rw [h2, h1, hvolB, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        rw [mul_assoc]
    _ ≤ _ := by
        apply ENNReal.rpow_le_rpow _ hr
        exact mul_le_mul_right hinner _

end

end CoarseDeGiorgi.SharpnessExamples
