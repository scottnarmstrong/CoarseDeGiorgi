import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicKernelSmooth
import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicFields
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Translation invariance of ordinary periodic-box integration -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Set

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The open fundamental box has the same measure restriction as its half-open version. -/
theorem reflectionBox_restrict_eq_pi (m : ℤ) (d : ℕ) :
    (volume : Measure (Vec d)).restrict (reflectionBox m) =
      Measure.pi (fun _ : Fin d => volume.restrict (Ioc (-auxSide m) (auxSide m))) := by
  have heq : reflectionBox (d := d) m = Set.univ.pi (fun _ => Ioo (-auxSide m) (auxSide m)) := by
    ext x
    simp only [reflectionBox, Set.mem_univ_pi, Set.mem_ofPred_eq, Set.mem_Ioo, abs_lt]
  rw [heq, volume_pi, Measure.restrict_pi_pi]
  congr 1
  funext i
  exact Measure.restrict_congr_set Ioo_ae_eq_Ioc

/-- Periodic nonnegative integrals over one interval do not depend on its starting point. -/
theorem setLIntegral_periodic_interval {P : ℝ} (hP : 0 < P) (a b : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Function.Periodic F P) :
    ∫⁻ t in Ioc a (a + P), F t = ∫⁻ t in Ioc b (b + P), F t := by
  let : VAddInvariantMeasure (AddSubgroup.zmultiples P) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  exact (isAddFundamentalDomain_Ioc hP a).setLIntegral_eq
    (isAddFundamentalDomain_Ioc hP b) F hF.map_vadd_zmultiples

/-- Translation followed by wrapping preserves the ordinary one-dimensional period measure. -/
theorem measurePreserving_wrapCoordinate_add (m : ℤ) (u : ℝ) :
    MeasurePreserving (fun t => wrapCoordinate m (t + u))
      (volume.restrict (Ioc (-auxSide m) (auxSide m)))
      (volume.restrict (Ioc (-auxSide m) (auxSide m))) := by
  refine ⟨(measurable_wrapCoordinate m).comp (measurable_id.add_const u), ?_⟩
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun t : ℝ => wrapCoordinate m (t + u)) :=
    (measurable_wrapCoordinate m).comp (measurable_id.add_const u)
  rw [Measure.map_apply hm hs]
  let F : ℝ → ℝ≥0∞ := fun t => s.indicator (fun _ => 1) (wrapCoordinate m t)
  have hp : Function.Periodic F (2 * auxSide m) := by
    intro t
    dsimp only [F]
    rw [wrapCoordinate_add_period]
  have hpre : (fun t : ℝ => t + u) ⁻¹' Ioc (-auxSide m + u) (auxSide m + u) =
      Ioc (-auxSide m) (auxSide m) := by
    ext t
    simp only [mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have ht := (measurePreserving_add_right (volume : Measure ℝ) u).restrict_preimage_emb
    (Homeomorph.addRight u).measurableEmbedding (Ioc (-auxSide m + u) (auxSide m + u))
  rw [hpre] at ht
  have hi := ht.lintegral_comp_emb (Homeomorph.addRight u).measurableEmbedding F
  have hperiod := setLIntegral_periodic_interval
    (mul_pos (by norm_num : (0 : ℝ) < 2) (auxSide_pos m))
    (-auxSide m + u) (-auxSide m) F hp
  rw [show -auxSide m + u + 2 * auxSide m = auxSide m + u by ring,
    show -auxSide m + 2 * auxSide m = auxSide m by ring] at hperiod
  have heq : ∫⁻ t in Ioc (-auxSide m) (auxSide m), F (t + u) =
      ∫⁻ t in Ioc (-auxSide m) (auxSide m), F t := hi.trans hperiod
  have hae : ∀ᵐ t ∂volume.restrict (Ioc (-auxSide m) (auxSide m)),
      wrapCoordinate m t = t := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact wrapCoordinate_eq_self m (abs_lt.mpr ht)
  have heq' : (∫⁻ t in Ioc (-auxSide m) (auxSide m),
      s.indicator (fun _ => 1) (wrapCoordinate m (t + u))) =
      ∫⁻ t in Ioc (-auxSide m) (auxSide m), s.indicator (fun _ => 1) t :=
    heq.trans (lintegral_congr_ae (hae.mono fun t ht => by
      change s.indicator (fun _ => 1) (wrapCoordinate m t) = _
      rw [ht]))
  have hind : (fun t => s.indicator (fun _ => (1 : ℝ≥0∞))
      (wrapCoordinate m (t + u))) =
      ((fun t => wrapCoordinate m (t + u)) ⁻¹' s).indicator (fun _ => 1) := by
    rfl
  rw [hind, lintegral_indicator (hs.preimage hm), lintegral_indicator hs] at heq'
  simpa only [setLIntegral_one] using heq'

/-- Coordinatewise translated wrapping preserves unnormalized reflected volume. -/
theorem measurePreserving_wrapBox_add (m : ℤ) (u : Vec d) :
    MeasurePreserving (fun x => wrapBox m (x + u))
      (volume.restrict (reflectionBox m)) (volume.restrict (reflectionBox m)) := by
  rw [reflectionBox_restrict_eq_pi]
  exact measurePreserving_pi _ _ (fun i => measurePreserving_wrapCoordinate_add m (u i))

/-- Negation preserves the reflected fundamental box and its ordinary measure. -/
theorem measurePreserving_neg_reflectionBox (m : ℤ) :
    MeasurePreserving (fun x : Vec d => -x)
      (volume.restrict (reflectionBox m)) (volume.restrict (reflectionBox m)) := by
  have heq : (fun x : Vec d => -x) ⁻¹' reflectionBox m = reflectionBox m := by
    ext x
    simp only [Set.mem_preimage, reflectionBox, Set.mem_ofPred_eq, Pi.neg_apply, abs_neg]
  have h := (Measure.measurePreserving_neg (volume : Measure (Vec d))).restrict_preimage_emb
    (Homeomorph.neg (Vec d)).measurableEmbedding (reflectionBox m)
  rwa [heq] at h

/-- Translated differences also preserve fundamental-box measure. -/
theorem measurePreserving_wrapBox_sub (m : ℤ) (u : Vec d) :
    MeasurePreserving (fun x => wrapBox m (u - x))
      (volume.restrict (reflectionBox m)) (volume.restrict (reflectionBox m)) := by
  simpa only [Function.comp_def, neg_add_eq_sub] using
    (measurePreserving_wrapBox_add m u).comp (measurePreserving_neg_reflectionBox m)

/-- Translation invariance for a measurable periodic nonnegative integrand. -/
theorem lintegral_periodicField_add (m : ℤ) (F : Vec d → ℝ≥0∞)
    (hF : Measurable F)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (u : Vec d) :
    ∫⁻ x in reflectionBox m, F (x + u) = ∫⁻ x in reflectionBox m, F x := by
  simpa only [periodicField_wrapBox m F hp] using
    (measurePreserving_wrapBox_add m u).lintegral_comp hF

/-- Both difference-variable integral orientations use the same periodic mass. -/
theorem lintegral_periodicField_sub (m : ℤ) (F : Vec d → ℝ≥0∞)
    (hF : Measurable F)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (u : Vec d) :
    ∫⁻ x in reflectionBox m, F (u - x) = ∫⁻ x in reflectionBox m, F x := by
  simpa only [periodicField_wrapBox m F hp] using
    (measurePreserving_wrapBox_sub m u).lintegral_comp hF

/-- Every Lᵖ norm on the periodic box is invariant under translations. -/
theorem eLpNorm_periodicField_add {E : Type*} [NormedAddCommGroup E]
    (m : ℤ) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (volume.restrict (reflectionBox m)))
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x)
    (u : Vec d) (p : ℝ≥0∞) :
    eLpNorm (fun x => F (x + u)) p (volume.restrict (reflectionBox m)) =
      eLpNorm F p (volume.restrict (reflectionBox m)) := by
  simpa only [Function.comp_def, periodicField_wrapBox m F hp] using
    eLpNorm_comp_measurePreserving hF (measurePreserving_wrapBox_add m u)

end

end CoarseDeGiorgi.Foundations.Reconstruction
