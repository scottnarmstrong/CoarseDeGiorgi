import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessSupersolution
import CoarseDeGiorgi.Statements.NonnegativeEssInf

/-! # Nonnegativity and the common essential infimum of the supersolutions -/

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem originCube_eq_ball_of_pos {d : ℕ} [NeZero d] {ρ : ℝ} (hρ : 0 < ρ) :
    originCube (d := d) ρ = Metric.ball (0 : Vec d) (ρ / 2) := by
  ext x
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by positivity)]
  simp only [originCube, mem_ofPred_eq, Real.norm_eq_abs, abs_lt]

/-- The common infimum `U_ε(d/16)`, computed with `ε = 1/16`. -/
def whM (d : ℕ) (q t : ℝ) : ℝ := whU d q t (1 / 16) ((d : ℝ) / 16)

theorem whk_eq_of_ge {d : ℕ} (q t : ℝ) {ε ε' σ : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (h : 4 * ε ^ 2 ≤ σ) (h' : 4 * ε' ^ 2 ≤ σ) : whk d q t ε σ = whk d q t ε' σ := by
  unfold whk
  rw [whP_eq_one hε h, whP_eq_one hε' h']

theorem four_sq_le {d : ℕ} (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    4 * ε ^ 2 ≤ (d : ℝ) / 16 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

theorem whU_at_cell {d : ℕ} (hd : 3 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    whU d q t ε ((d : ℝ) / 16) = whM d q t := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold whM whU
  apply intervalIntegral.integral_congr
  intro σ hσ
  have hσ' : (d : ℝ) / 16 ≤ σ := by
    rw [uIcc_of_le (by linarith)] at hσ
    exact hσ.1
  exact whk_eq_of_ge q t hε (by norm_num) (le_trans (four_sq_le hd hε hε8) hσ') (by nlinarith)

theorem whM_pos {d : ℕ} (hd : 3 ≤ d) (q t : ℝ) : 0 < whM d q t := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := by omega
  unfold whM whU
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (whk_intervalIntegrable q t (by norm_num : (0 : ℝ) < 1 / 16) (by linarith) (by linarith))
    (fun σ hσ => ?_) (by linarith)
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hAs := whAs_pos (d := d) (q := q) (t := t) hσ0 (by linarith [hσ.2])
  unfold whk whK
  rw [whP_eq_one (by norm_num) (by nlinarith [hσ.1])]
  have := whQ_pos (d := d) hσ0
  positivity

theorem whu_nonneg_of_mem {d : ℕ} [NeZero d] (q t : ℝ) {ε : ℝ} {x : Vec d}
    (hx : x ∈ originCube (d := d) 1) : 0 ≤ whu d q t ε x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have := vecNormSq_lt_of_mem hx
  unfold whu whU
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun u hu => whk_nonneg q t (by linarith [hu.2]))

theorem whu_ge_on_half {d : ℕ} [NeZero d] (hd : 3 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε < 1 / 8) {x : Vec d} (hx : x ∈ originCube (d := d) (1 / 2)) :
    whM d q t ≤ whu d q t ε x := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hxn : ‖x‖ < 1 / 4 := by
    rw [originCube_eq_ball_of_pos (by norm_num), mem_ball_zero_iff] at hx
    linarith
  have hσ : vecNormSq x ≤ (d : ℝ) / 16 := by
    have h1 := vecNormSq_le x
    have h2 : ‖x‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg x]
    nlinarith
  rw [← whU_at_cell hd q t hε hε8]
  exact whU_antitone (by omega) q t hε hσ (by linarith)

theorem whEssInf {d : ℕ} [NeZero d] (hd : 3 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε < 1 / 8) :
    nonnegativeEssInf (originCube (d := d) (1 / 2)) (whu d q t ε) =
      ENNReal.ofReal (whM d q t) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := by omega
  have hW : MeasurableSet (originCube (d := d) (1 / 2)) := by
    rw [originCube_eq_ball_of_pos (by norm_num)]; exact Metric.isOpen_ball.measurableSet
  have hM := whM_pos hd q t
  unfold nonnegativeEssInf
  apply le_antisymm
  · -- the upper bound
    refine ENNReal.le_of_forall_pos_le_add (fun δ hδ _ => ?_)
    by_contra hcon
    rw [not_le] at hcon
    have hlt := ae_lt_of_lt_essInf hcon
    have hlt' : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ originCube (d := d) (1 / 2) →
        ENNReal.ofReal (whM d q t) + δ < ENNReal.ofReal (whu d q t ε x) :=
      (ae_restrict_iff' hW).1 hlt
    -- the vertex approximation
    have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
    have hcont : ContinuousAt (whU d q t ε) ((d : ℝ) / 16) :=
      (hasDerivAt_whU hd1 q t hε (by linarith)).continuousAt
    have hlim : Tendsto (fun τ : ℝ => (d : ℝ) * (1 / 4 - τ) ^ 2) (𝓝 0) (𝓝 ((d : ℝ) / 16)) := by
      have : Continuous (fun τ : ℝ => (d : ℝ) * (1 / 4 - τ) ^ 2) := by fun_prop
      have h0 := this.tendsto 0
      convert h0 using 2
      ring
    have hlim2 : Tendsto (fun τ : ℝ => whU d q t ε ((d : ℝ) * (1 / 4 - τ) ^ 2)) (𝓝 0)
        (𝓝 (whM d q t)) := by
      rw [← whU_at_cell hd q t hε hε8]
      exact hcont.tendsto.comp hlim
    have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), whU d q t ε ((d : ℝ) * (1 / 4 - τ) ^ 2) < whM d q t + δ :=
      (hlim2.eventually (gt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds
    obtain ⟨τ, hτ1, hτ2⟩ := (hev.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
    have hτ : τ ∈ Ioo (0 : ℝ) (1 / 4) := hτ2
    set x0 : Vec d := fun _ => 1 / 4 - τ with hx0
    have hx0n : ‖x0‖ = 1 / 4 - τ := by
      rw [hx0, pi_norm_const, Real.norm_eq_abs, abs_of_pos (by linarith [hτ.2])]
    have hx0W : x0 ∈ originCube (d := d) (1 / 2) := by
      rw [originCube_eq_ball_of_pos (by norm_num), mem_ball_zero_iff]
      linarith [hτ.1]
    have hx0σ : vecNormSq x0 = (d : ℝ) * (1 / 4 - τ) ^ 2 := by
      rw [vecNormSq_eq_sum]; simp [hx0]
    have hx0O : x0 ∈ whO d := by
      show vecNormSq x0 < d
      rw [hx0σ]
      have : (1 / 4 - τ) ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
      nlinarith
    have hopen : IsOpen (originCube (d := d) (1 / 2) ∩
        (whO d ∩ whu d q t ε ⁻¹' Iio (whM d q t + δ))) := by
      rw [originCube_eq_ball_of_pos (by norm_num)]
      exact Metric.isOpen_ball.inter
        ((whu_continuousOn q t hε).isOpen_inter_preimage isOpen_whO isOpen_Iio)
    have hmem : x0 ∈ originCube (d := d) (1 / 2) ∩
        (whO d ∩ whu d q t ε ⁻¹' Iio (whM d q t + δ)) := by
      refine ⟨hx0W, hx0O, ?_⟩
      show whu d q t ε x0 < whM d q t + δ
      unfold whu
      rw [hx0σ]
      exact hτ1
    have hpos := hopen.measure_pos volume ⟨x0, hmem⟩
    have hnull : volume (originCube (d := d) (1 / 2) ∩
        (whO d ∩ whu d q t ε ⁻¹' Iio (whM d q t + δ))) = 0 := by
      apply measure_mono_null _ (ae_iff.1 hlt')
      intro x hx hcontra
      have h1 := hcontra hx.1
      have h2 : whu d q t ε x < whM d q t + δ := hx.2.2
      have hge : 0 ≤ whM d q t + δ := by linarith
      rw [show ENNReal.ofReal (whM d q t) + δ = ENNReal.ofReal (whM d q t + δ) by
        rw [ENNReal.ofReal_add hM.le hδ'.le]; simp] at h1
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hge).1 h1
      linarith
    exact hpos.ne' hnull
  · -- the lower bound
    refine le_essInf_of_ae_le _ ?_
    filter_upwards [ae_restrict_mem hW] with x hx
    exact ENNReal.ofReal_le_ofReal (whu_ge_on_half hd q t hε hε8 hx)

end

end CoarseDeGiorgi.SharpnessExamples
