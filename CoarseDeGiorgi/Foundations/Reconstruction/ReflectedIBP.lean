module

public import CoarseDeGiorgi.Foundations.Reconstruction.OrthantDecomposition

/-! # Integration by parts on the reflected fundamental box with an L¹ gradient -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The even reflection, before periodic continuation. -/
def reflectedScalar (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (x : Vec d) : ℝ :=
  w (auxLower m z + fun i => |x i|)

/-- One coordinate of the reflected weak gradient. Values on reflection planes are immaterial. -/
def reflectedPartial (m : ℤ) (z : Fin d → ℤ) (Dw : Vec d → Vec d)
    (i : Fin d) (x : Vec d) : ℝ :=
  reflectionSign (decide (0 < x i)) * Dw (auxLower m z + fun j => |x j|) i

theorem reflectedScalar_signLinear (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ)
    (s : Fin d → Bool) {x : Vec d} (hx : x ∈ reflectionPositiveBox m) :
    reflectedScalar m z w (signLinear s x) = w (auxLower m z + x) := by
  unfold reflectedScalar
  rw [abs_signLinear_of_mem_positive m s hx]

theorem reflectedPartial_signLinear (m : ℤ) (z : Fin d → ℤ) (Dw : Vec d → Vec d)
    (i : Fin d) (s : Fin d → Bool) {x : Vec d} (hx : x ∈ reflectionPositiveBox m) :
    reflectedPartial m z Dw i (signLinear s x) =
      reflectionSign (s i) * Dw (auxLower m z + x) i := by
  unfold reflectedPartial
  rw [abs_signLinear_of_mem_positive m s hx, signLinear_apply]
  congr 2
  cases hs : s i
  · have hn : ¬0 < -x i := not_lt.mpr (le_of_lt (neg_neg_of_pos (hx i).1))
    simp only [reflectionSign, Bool.false_eq_true, ite_false, neg_one_mul, hn, decide_false]
  · simp only [reflectionSign, ite_true, one_mul, (hx i).1, decide_true]

/-- Translation from the positive reflection cell preserves restricted volume exactly. -/
theorem measurePreserving_auxLower_add (m : ℤ) (z : Fin d → ℤ) :
    MeasurePreserving (fun x => auxLower m z + x)
      (volume.restrict (reflectionPositiveBox m)) (volume.restrict (auxCube m z)) := by
  have h := (measurePreserving_add_left (volume : Measure (Vec d)) (auxLower m z)).restrict_preimage_emb
    (Homeomorph.addLeft (auxLower m z)).measurableEmbedding (auxCube m z)
  simpa only [← reflectionPositiveBox_eq_preimage_auxCube m z] using h

/-- Every continuous multiplier is bounded on a prescribed finite ball. -/
theorem integrableOn_mul_continuous_ball {U : Set (Vec d)} {w g : Vec d → ℝ}
    {c : Vec d} {R : ℝ} (hw : IntegrableOn w U volume) (hg : Continuous g)
    (hUmeas : MeasurableSet U) (hU : U ⊆ Metric.closedBall c R) : IntegrableOn (fun x => w x * g x) U volume := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  apply hw.mul_bdd hg.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hUmeas] with x hx
  exact hM x (hU hx)

theorem reflectionPositiveBox_subset_closedBall (m : ℤ) :
    reflectionPositiveBox (d := d) m ⊆ Metric.closedBall 0 (auxSide m) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (auxSide_pos m).le).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_pos (hx i).1]
  exact (hx i).2.le

/-- Cellwise pullbacks characterize integrability on the reflected box. -/
theorem integrableOn_reflectionBox_of_pullbacks (m : ℤ) (f : Vec d → ℝ)
    (hf : ∀ s : Fin d → Bool,
      IntegrableOn (fun x => f (signLinear s x)) (reflectionPositiveBox m) volume) :
    IntegrableOn f (reflectionBox m) volume := by
  rw [integrableOn_reflectionBox_iff]
  intro s
  have h := (measurePreserving_signLinear_restrict m s).integrable_comp_of_integrable (hf s)
  have hinv (x : Vec d) := signLinear_involutive s x
  simpa only [IntegrableOn, Function.comp_def, hinv] using h

/-- Even reflection of an L¹ scalar is L¹ on the whole reflected box. -/
theorem integrableOn_reflectedScalar {m : ℤ} {z : Fin d → ℤ} {w : Vec d → ℝ}
    (hw : IntegrableOn w (auxCube m z) volume) :
    IntegrableOn (reflectedScalar m z w) (reflectionBox m) volume := by
  have hwp := (measurePreserving_auxLower_add m z).integrable_comp_of_integrable hw
  apply integrableOn_reflectionBox_of_pullbacks
  intro s
  apply hwp.congr
  filter_upwards [ae_restrict_mem (isOpen_reflectionPositiveBox m).measurableSet] with x hx
  exact (reflectedScalar_signLinear m z w s hx).symm

/-- The reflected gradient coordinate uses only the original L¹ vector hypothesis. -/
theorem integrableOn_reflectedPartial {m : ℤ} {z : Fin d → ℤ} {Dw : Vec d → Vec d}
    (hDw : IntegrableOn Dw (auxCube m z) volume) (i : Fin d) :
    IntegrableOn (reflectedPartial m z Dw i) (reflectionBox m) volume := by
  have hDp := (measurePreserving_auxLower_add m z).integrable_comp_of_integrable (hDw.eval i)
  apply integrableOn_reflectionBox_of_pullbacks
  intro s
  apply (hDp.const_mul (reflectionSign (s i))).congr
  filter_upwards [ae_restrict_mem (isOpen_reflectionPositiveBox m).measurableSet] with x hx
  exact (reflectedPartial_signLinear m z Dw i s hx).symm

/-- Integration by parts against smooth periodic tests on the ordinary reflected box. -/
theorem reflected_integration_by_parts {m : ℤ} {z : Fin d → ℤ}
    {w : Vec d → ℝ} {Dw : Vec d → Vec d}
    (hweak : HasWeakGradientOn (auxCube m z) w Dw)
    (hw : IntegrableOn w (auxCube m z) volume)
    (hDw : IntegrableOn Dw (auxCube m z) volume) (i : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hperiod : ∀ y, φ (y + (2 * auxSide m) • basisVec i) = φ y) :
    ∫ x in reflectionBox m, reflectedScalar m z w x * (fderiv ℝ φ x) (basisVec i) ∂volume =
      -∫ x in reflectionBox m, reflectedPartial m z Dw i x * φ x ∂volume := by
  let W : Vec d → ℝ := fun x => w (auxLower m z + x)
  let G : Vec d → ℝ := fun x => Dw (auxLower m z + x) i
  have hW : IntegrableOn W (reflectionPositiveBox m) volume :=
    (measurePreserving_auxLower_add m z).integrable_comp_of_integrable hw
  have hG : IntegrableOn G (reflectionPositiveBox m) volume :=
    (measurePreserving_auxLower_add m z).integrable_comp_of_integrable (hDw.eval i)
  have hD : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hWI (s : Fin d → Bool) : IntegrableOn
      (fun x => W x * (fderiv ℝ φ (signLinear s x)) (basisVec i))
      (reflectionPositiveBox m) volume :=
    integrableOn_mul_continuous_ball hW (hD.comp (signLinear s).continuous)
      (isOpen_reflectionPositiveBox m).measurableSet (reflectionPositiveBox_subset_closedBall m)
  have hGI (s : Fin d → Bool) : IntegrableOn
      (fun x => G x * (reflectionSign (s i) * φ (signLinear s x)))
      (reflectionPositiveBox m) volume :=
    integrableOn_mul_continuous_ball hG
      (continuous_const.mul (hφ.continuous.comp (signLinear s).continuous))
      (isOpen_reflectionPositiveBox m).measurableSet (reflectionPositiveBox_subset_closedBall m)
  have hleft (s : Fin d → Bool) : IntegrableOn
      (fun x => reflectedScalar m z w x * (fderiv ℝ φ x) (basisVec i))
      (reflectionOrthant m s) volume := by
    have hpos : IntegrableOn (fun x => reflectedScalar m z w (signLinear s x) *
        (fderiv ℝ φ (signLinear s x)) (basisVec i)) (reflectionPositiveBox m) volume := by
      apply (hWI s).congr
      filter_upwards [ae_restrict_mem (isOpen_reflectionPositiveBox m).measurableSet] with x hx
      dsimp only [W]
      rw [reflectedScalar_signLinear m z w s hx]
    have h := (measurePreserving_signLinear_restrict m s).integrable_comp_of_integrable hpos
    have hinv (x : Vec d) := signLinear_involutive s x
    simpa only [IntegrableOn, Function.comp_def, hinv] using h
  have hright (s : Fin d → Bool) : IntegrableOn
      (fun x => reflectedPartial m z Dw i x * φ x) (reflectionOrthant m s) volume := by
    have hpos : IntegrableOn (fun x => reflectedPartial m z Dw i (signLinear s x) *
        φ (signLinear s x)) (reflectionPositiveBox m) volume := by
      apply (hGI s).congr
      filter_upwards [ae_restrict_mem (isOpen_reflectionPositiveBox m).measurableSet] with x hx
      dsimp only [G]
      rw [reflectedPartial_signLinear m z Dw i s hx]
      ring
    have h := (measurePreserving_signLinear_restrict m s).integrable_comp_of_integrable hpos
    have hinv (x : Vec d) := signLinear_involutive s x
    simpa only [IntegrableOn, Function.comp_def, hinv] using h
  have hfold := weakGradient_folded_identity hweak hw hDw i hφ hperiod
  have hμ := measurePreserving_auxLower_add m z
  have hchangeL := hμ.integral_comp (Homeomorph.addLeft (auxLower m z)).measurableEmbedding
    (fun x => w x * ∑ s : Fin d → Bool,
      (fderiv ℝ φ (signLinear s (x - auxLower m z))) (basisVec i))
  have hchangeR := hμ.integral_comp (Homeomorph.addLeft (auxLower m z)).measurableEmbedding
    (fun x => Dw x i * translatedFoldedTest m z i φ x)
  simp only [translatedFoldedTest, add_sub_cancel_left] at hchangeL hchangeR
  simp only [translatedFoldedTest] at hfold
  rw [← hchangeL, ← hchangeR] at hfold
  change (∫ x in reflectionPositiveBox m, W x * ∑ s : Fin d → Bool,
    (fderiv ℝ φ (signLinear s x)) (basisVec i) ∂volume) =
    -∫ x in reflectionPositiveBox m, G x * foldedTest i φ x ∂volume at hfold
  simp only [foldedTest, Finset.mul_sum] at hfold
  rw [integral_finsetSum Finset.univ (fun s _ => hWI s),
    integral_finsetSum Finset.univ (fun s _ => hGI s)] at hfold
  rw [setIntegral_reflectionBox_eq_sum m _ hleft,
    setIntegral_reflectionBox_eq_sum m _ hright]
  have heqL : (∑ s : Fin d → Bool, ∫ x in reflectionPositiveBox m,
      reflectedScalar m z w (signLinear s x) * (fderiv ℝ φ (signLinear s x)) (basisVec i) ∂volume) =
      ∑ s : Fin d → Bool, ∫ x in reflectionPositiveBox m,
        W x * (fderiv ℝ φ (signLinear s x)) (basisVec i) ∂volume := by
    apply Finset.sum_congr rfl
    intro s _
    apply setIntegral_congr_fun (isOpen_reflectionPositiveBox m).measurableSet
    intro x hx
    dsimp only [W]
    rw [reflectedScalar_signLinear m z w s hx]
  have heqR : (∑ s : Fin d → Bool, ∫ x in reflectionPositiveBox m,
      reflectedPartial m z Dw i (signLinear s x) * φ (signLinear s x) ∂volume) =
      ∑ s : Fin d → Bool, ∫ x in reflectionPositiveBox m,
        G x * (reflectionSign (s i) * φ (signLinear s x)) ∂volume := by
    apply Finset.sum_congr rfl
    intro s _
    apply setIntegral_congr_fun (isOpen_reflectionPositiveBox m).measurableSet
    intro x hx
    dsimp only [G]
    rw [reflectedPartial_signLinear m z Dw i s hx]
    ring
  rw [heqL, heqR]
  exact hfold

end

end CoarseDeGiorgi.Foundations.Reconstruction
