module

public import CoarseDeGiorgi.Foundations.Reconstruction.FineKernelDeriv

/-! # Smooth parameter integrals over a compact interval

Compactness gives local uniform dominators. Induction differentiates the
integral into the complete space of continuous linear maps.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuity of a compact-interval integral of a jointly continuous function. -/
theorem continuous_integral_Icc_joint (F : ℝ × Vec d → E) (hF : Continuous F) (a b : ℝ) :
    Continuous (fun x => ∫ t in Set.Icc a b, F (t, x) ∂volume) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_closedBall x 1)).exists_bound_of_continuousOn hF.continuousOn
  have hm (y : Vec d) : IntegrableOn (fun t => F (t, y)) (Set.Icc a b) volume :=
    (hF.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_Icc
  apply continuousAt_of_dominated (bound := fun _ => M)
    (Eventually.of_forall fun y => (hm y).aestronglyMeasurable)
  · filter_upwards [Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hM (t, y) ⟨ht, hy⟩
  · exact integrable_const _
  · exact ae_of_all _ fun t => (hF.comp (continuous_const.prodMk continuous_id)).continuousAt

/-- The spatial part of the derivative of a function on time × space. -/
def spatialFDeriv (F : ℝ × Vec d → E) (p : ℝ × Vec d) : Vec d →L[ℝ] E :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ (Vec d))

theorem hasFDerivAt_spatial (F : ℝ × Vec d → E) {p : ℝ × Vec d}
    (hF : DifferentiableAt ℝ F p) :
    HasFDerivAt (fun x => F (p.1, x)) (spatialFDeriv F p) p.2 := by
  exact hF.hasFDerivAt.comp p.2
    ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))

theorem contDiff_spatialFDeriv {n : ℕ} (F : ℝ × Vec d → E)
    (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (spatialFDeriv F) := by
  exact (hF.fderiv_right (m := n) (by simp)).clm_comp contDiff_const

/-- Differentiation of a jointly C¹ function under a compact-interval integral. -/
theorem hasFDerivAt_integral_Icc_joint (F : ℝ × Vec d → E) (hF : ContDiff ℝ 1 F)
    (a b : ℝ) (x : Vec d) :
    HasFDerivAt (fun y => ∫ t in Set.Icc a b, F (t, y) ∂volume)
      (∫ t in Set.Icc a b, spatialFDeriv F (t, x) ∂volume) x := by
  have hD : Continuous (spatialFDeriv F) :=
    (contDiff_spatialFDeriv (n := 0) F hF).continuous
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_closedBall x 1)).exists_bound_of_continuousOn hD.continuousOn
  have hm (y : Vec d) : IntegrableOn (fun t => F (t, y)) (Set.Icc a b) volume :=
    (hF.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_Icc
  have hDm : IntegrableOn (fun t => spatialFDeriv F (t, x)) (Set.Icc a b) volume :=
    (hD.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_Icc
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x 1) (Metric.closedBall_mem_nhds x (by norm_num))
    (Eventually.of_forall fun y => (hm y).aestronglyMeasurable) (hm x)
    hDm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht y hy
    exact hM (t, y) ⟨ht, hy⟩
  · exact integrable_const _
  · exact ae_of_all _ fun t y _ => hasFDerivAt_spatial F
      ((hF.differentiable (by norm_num)) (t, y))

/-- Joint Cⁿ regularity passes through integration over a fixed compact interval. -/
theorem contDiff_integral_Icc_joint (n : ℕ) (F : ℝ × Vec d → E)
    (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun x => ∫ t in Set.Icc a b, F (t, x) ∂volume) := by
  induction n generalizing E with
  | zero =>
    exact contDiff_zero.mpr (continuous_integral_Icc_joint F hF.continuous a b)
  | succ n ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ t in Set.Icc a b, spatialFDeriv F (t, x) ∂volume, ?_, ?_⟩
    · exact ih (spatialFDeriv F) (contDiff_spatialFDeriv F hF)
    · exact hasFDerivAt_integral_Icc_joint F (hF.of_le (by simp)) a b

end

end CoarseDeGiorgi.Foundations.Reconstruction
