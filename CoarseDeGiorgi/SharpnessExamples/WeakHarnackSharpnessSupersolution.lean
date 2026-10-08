import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessGradient
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.IsSmoothCore
import CoarseDeGiorgi.Statements.MemH1a

/-! # The weak Harnack supersolutions lie in `H¹_a` and are weighted supersolutions -/

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem weightedEnergy_eq_zero_of_zero {d : ℕ} (a : CoeffField d) {V : Set (Vec d)}
    (hV : MeasurableSet V) (G : Vec d → Vec d) (hG : ∀ x ∈ V, G x = 0) :
    weightedEnergy a V G = 0 := by
  unfold weightedEnergy
  rw [setLIntegral_congr_fun hV (g := fun _ => 0) (fun x hx => by rw [hG x hx, vecDot_zero_left]; simp)]
  simp

theorem memH1a_of_core {d : ℕ} (a : CoeffField d) {V : Set (Vec d)} (hV : MeasurableSet V)
    {w : Vec d → ℝ} {G' : Vec d → Vec d}
    (hw : AEStronglyMeasurable w (volume.restrict V))
    (hG : AEStronglyMeasurable G' (volume.restrict V))
    (hcore : IsSmoothCore a V w) (hGw : ∀ x ∈ V, G' x = smoothGrad w x) :
    MemH1a a V w G' := by
  refine ⟨hw, hG, fun _ => w, fun _ => hcore, ?_, ?_, ?_⟩
  · intro ε hε
    refine ⟨0, fun m n _ _ => ?_⟩
    have h1 : weightedEnergy a V (fun x => smoothGrad w x - smoothGrad w x) = 0 :=
      weightedEnergy_eq_zero_of_zero a hV _ (fun x _ => sub_self _)
    have h2 : volumeAverage V (fun x => w x - w x) = 0 := by
      simp [volumeAverage]
    rw [h1, h2]
    simpa using ENNReal.ofReal_pos.2 hε
  · intro K _ _
    simp
  · have h1 : ∀ n : ℕ, weightedEnergy a V (fun x => smoothGrad w x - G' x) = 0 := fun _ =>
      weightedEnergy_eq_zero_of_zero a hV _ (fun x hx => by rw [hGw x hx]; exact sub_self _)
    exact tendsto_const_nhds.congr (fun n => (h1 n).symm)

theorem smoothGrad_neg {d : ℕ} (f : Vec d → ℝ) (x : Vec d) :
    smoothGrad (fun y => -f y) x = -smoothGrad f x := by
  funext i
  unfold smoothGrad
  rw [fderiv_fun_neg]
  rfl

theorem smoothGrad_eq_zero_of_notMem {d : ℕ} {φ : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport φ) :
    smoothGrad φ x = 0 := by
  funext i
  unfold smoothGrad
  rw [fderiv_of_notMem_tsupport ℝ hx]
  rfl

/-- The closed cube `[-1/2, 1/2]^d`. -/
def whK0 (d : ℕ) : Set (Vec d) := Set.Icc (fun _ => (-1 / 2 : ℝ)) (fun _ => 1 / 2)

theorem originCube_subset_whK0 {d : ℕ} : originCube (d := d) 1 ⊆ whK0 d := by
  intro x hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · show (-1 / 2 : ℝ) ≤ x i
    linarith [(hx i).1]
  · exact (hx i).2.le

theorem whK0_subset_whO {d : ℕ} [NeZero d] : whK0 d ⊆ whO d := by
  intro x hx
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  show vecNormSq x < d
  rw [vecNormSq_eq_sum]
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin d, (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h1 := hx.1 i
        have h2 := hx.2 i
        nlinarith
    _ = d / 4 := by simp; ring
    _ < d := by linarith

theorem whu_continuousOn {d : ℕ} [NeZero d] (q t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (whu d q t ε) (whO d) :=
  (contDiffOn_whu (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) q t hε).continuousOn

theorem whu_neg_energy_lt_top {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t) {ε : ℝ}
    (hε : 0 < ε) :
    weightedEnergy (whCoeff d q t) (originCube 1) (smoothGrad (fun x => -whu d q t ε x)) < ⊤ := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (d : ℝ) / 4)).exists_bound_of_continuousOn
    ((contDiffOn_whk (d := d) q t hε).continuousOn.mono
      (fun σ hσ => show σ < d by have := hσ.2; linarith))
  set Mb : ℝ := (Real.exp 1 * whR d) ^ whBeta d q t / (whBeta d q t / 3) ^ 3 with hMb
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, by linarith⟩)
  have hMb0 : 0 ≤ Mb := div_nonneg
    (Real.rpow_nonneg (mul_nonneg (Real.exp_pos 1).le (whR_pos hd).le) _) (by positivity)
  have hpt : ∀ x ∈ originCube (d := d) 1,
      vecDot (smoothGrad (fun y => -whu d q t ε y) x)
        (matVecMul (whCoeff d q t x) (smoothGrad (fun y => -whu d q t ε y) x)) ≤
      Mb * (d * B ^ 2) := by
    intro x hx
    have hx0 := mem_whO_of_mem hx
    have hxn : ‖x‖ < 1 / 2 := (mem_originCube_iff x).1 hx
    have hσ : vecNormSq x ∈ Icc (0 : ℝ) ((d : ℝ) / 4) := by
      refine ⟨?_, (vecNormSq_lt_of_mem hx).le⟩
      rw [vecNormSq_eq_sum]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hk := hB _ hσ
    rw [Real.norm_eq_abs] at hk
    have hg : smoothGrad (fun y => -whu d q t ε y) x = fun i => 2 * whk d q t ε (vecNormSq x) * x i := by
      rw [smoothGrad_neg]
      funext i
      rw [Pi.neg_apply, smoothGrad_whu hd q t hε hx0]
      ring
    have hc0 := whField_nonneg d q t (euclidNorm x)
    have hc1 : whField d q t (euclidNorm x) ≤ Mb :=
      whField_le hd hβ (euclidNorm_nonneg' x) (norm_lt_R_of_mem hx)
    have hmv : matVecMul (whCoeff d q t x) (smoothGrad (fun y => -whu d q t ε y) x) =
        whField d q t (euclidNorm x) • smoothGrad (fun y => -whu d q t ε y) x :=
      matVecMul_scalarMatrix _ _
    rw [hmv, vecDot_smul_right]
    have hsum : vecDot (smoothGrad (fun y => -whu d q t ε y) x)
        (smoothGrad (fun y => -whu d q t ε y) x) ≤ d * B ^ 2 := by
      rw [hg]
      unfold vecDot
      calc ∑ i, 2 * whk d q t ε (vecNormSq x) * x i * (2 * whk d q t ε (vecNormSq x) * x i)
          ≤ ∑ _i : Fin d, B ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hxi : |x i| ≤ 1 / 2 := by
              have := norm_le_pi_norm x i
              rw [Real.norm_eq_abs] at this
              linarith
            have h1 : |2 * whk d q t ε (vecNormSq x) * x i| ≤ B := by
              rw [abs_mul, abs_mul]
              have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
              rw [this]
              nlinarith [abs_nonneg (whk d q t ε (vecNormSq x)), abs_nonneg (x i)]
            calc _ = |2 * whk d q t ε (vecNormSq x) * x i| ^ 2 := by rw [sq_abs]; ring
              _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = d * B ^ 2 := by simp
    have hdot0 : 0 ≤ vecDot (smoothGrad (fun y => -whu d q t ε y) x)
        (smoothGrad (fun y => -whu d q t ε y) x) := by
      unfold vecDot
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact mul_le_mul hc1 hsum hdot0 hMb0
  unfold weightedEnergy
  calc ∫⁻ x in originCube (d := d) 1, ENNReal.ofReal (vecDot (smoothGrad (fun y => -whu d q t ε y) x)
        (matVecMul (whCoeff d q t x) (smoothGrad (fun y => -whu d q t ε y) x)))
      ≤ ∫⁻ _x in originCube (d := d) 1, ENNReal.ofReal (Mb * (d * B ^ 2)) := by
        apply setLIntegral_mono measurable_const
        intro x hx
        exact ENNReal.ofReal_le_ofReal (hpt x hx)
    _ = ENNReal.ofReal (Mb * (d * B ^ 2)) * volume (originCube (d := d) 1) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top volume_originCube_ne_top.lt_top

theorem whu_neg_isSmoothCore {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t) {ε : ℝ}
    (hε : 0 < ε) :
    IsSmoothCore (whCoeff d q t) (originCube 1) (fun x => -whu d q t ε x) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hV : originCube (d := d) 1 ⊆ whO d := fun x hx => mem_whO_of_mem hx
  refine ⟨?_, ?_, whu_neg_energy_lt_top hβ hε⟩
  · exact ((contDiffOn_whu hd q t hε).neg).mono hV
  · have hc : ContinuousOn (fun x => -whu d q t ε x) (whK0 d) :=
      ((whu_continuousOn q t hε).mono whK0_subset_whO).neg
    exact (hc.integrableOn_compact isCompact_Icc).mono_set originCube_subset_whK0

theorem whu_isWeightedSupersolution {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t)
    {ε : ℝ} (hε : 0 < ε) :
    IsWeightedSupersolution (whCoeff d q t) (originCube 1) (whu d q t ε)
      (smoothGrad (whu d q t ε)) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hV : originCube (d := d) 1 ⊆ whO d := fun x hx => mem_whO_of_mem hx
  unfold IsWeightedSupersolution IsWeightedSubsolution
  refine ⟨?_, ?_⟩
  · refine memH1a_of_core _ measurableSet_originCube ?_ ?_ (whu_neg_isSmoothCore hβ hε)
      (fun x _ => (smoothGrad_neg _ x).symm)
    · exact (((whu_continuousOn q t hε).mono hV).neg).aestronglyMeasurable measurableSet_originCube
    · have hfd : ContinuousOn (fderiv ℝ (whu d q t ε)) (whO d) :=
        (contDiffOn_whu hd q t hε).continuousOn_fderiv_of_isOpen isOpen_whO (by simp)
      have hg : ContinuousOn (fun x => smoothGrad (whu d q t ε) x) (whO d) := by
        refine continuousOn_pi.2 (fun i => ?_)
        exact hfd.clm_apply continuousOn_const
      exact ((hg.mono hV).neg).aestronglyMeasurable measurableSet_originCube
  · intro φ hφ hc hs hn
    have hpt : ∀ x : Vec d,
        vecDot (smoothGrad φ x) (matVecMul (whCoeff d q t x) ((fun x => -smoothGrad (whu d q t ε) x) x)) =
        vecDot (smoothGrad φ x) (whF d ε x) := by
      intro x
      by_cases hx : x ∈ tsupport φ
      · have := whFlux_identity (q := q) (t := t) hε (hs hx)
        simp only
        rw [this]
      · simp only
        rw [smoothGrad_eq_zero_of_notMem hx, vecDot_zero_left, vecDot_zero_left]
    obtain ⟨hint, hle⟩ := whFlux_test_nonpos hε hφ hc hs hn
    have hfun : (fun x => vecDot (smoothGrad φ x)
        (matVecMul (whCoeff d q t x) ((fun x => -smoothGrad (whu d q t ε) x) x))) =
        fun x => vecDot (smoothGrad φ x) (whF d ε x) := funext hpt
    rw [hfun]
    refine ⟨hint.integrableOn, ?_⟩
    have hz : ∀ x ∉ originCube (d := d) 1, vecDot (smoothGrad φ x) (whF d ε x) = 0 := by
      intro x hx
      rw [smoothGrad_eq_zero_of_notMem (fun h => hx (hs h)), vecDot_zero_left]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact hle

end

end CoarseDeGiorgi.SharpnessExamples
