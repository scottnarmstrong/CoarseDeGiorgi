import CoarseDeGiorgi.Weighted.Truncation.Chain
import CoarseDeGiorgi.Weighted.Truncation.PositivePart
import CoarseDeGiorgi.Weighted.PairOperations
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.LowerFractional.CubeDomain
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

private def smoothLogC (ε : ℝ) : ℝ := -ε / 3
private def smoothLogDelta (ε : ℝ) : ℝ := ε / 6
private def smoothLogB (ε : ℝ) : ℝ :=
  ε - GApprox (smoothLogC ε) (smoothLogDelta ε) 0
private def smoothLogArgument (ε t : ℝ) : ℝ :=
  smoothLogB ε + GApprox (smoothLogC ε) (smoothLogDelta ε) t
private def logExtension (ε : ℝ) : ℝ → ℝ := Real.log ∘ smoothLogArgument ε

private theorem gApprox_nonneg {c δ t : ℝ} (hδ : 0 < δ) : 0 ≤ GApprox c δ t := by
  by_cases hct : c ≤ t
  · exact intervalIntegral.integral_nonneg_of_forall hct (gStep_nonneg c δ)
  · have hz : (∫ x in Set.Ioc t c, gStep c δ x) = 0 := by
      rw [setIntegral_eq_zero_of_forall_eq_zero]
      intro x hx
      exact gStep_eq_zero hδ (by linarith only [hx.2, hδ])
    have hzero : GApprox c δ t = 0 := by
      unfold GApprox
      rw [intervalIntegral.integral_symm,
        intervalIntegral.integral_of_le (le_of_not_ge hct), hz]
      simp
    rw [hzero]

private theorem smoothLogB_lower {ε : ℝ} (hε : 0 < ε) :
    2 * ε / 3 ≤ smoothLogB ε := by
  have hδ : 0 < smoothLogDelta ε := by dsimp [smoothLogDelta]; positivity
  have hG : GApprox (smoothLogC ε) (smoothLogDelta ε) 0 ≤ ε / 3 := by
    calc
      GApprox (smoothLogC ε) (smoothLogDelta ε) 0 ≤
          |GApprox (smoothLogC ε) (smoothLogDelta ε) 0| := le_abs_self _
      _ ≤ |0 - smoothLogC ε| := abs_GApprox_le _ _ _
      _ = ε / 3 := by
        dsimp [smoothLogC]
        rw [abs_of_nonneg (by linarith [hε])]
        ring
  dsimp [smoothLogB]
  linarith

private theorem smoothLogArgument_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < smoothLogArgument ε t := by
  have hB := smoothLogB_lower hε
  have hδ : 0 < smoothLogDelta ε := by dsimp [smoothLogDelta]; positivity
  have hG := gApprox_nonneg hδ (c := smoothLogC ε) (t := t)
  dsimp [smoothLogArgument]
  linarith

private theorem smoothLogArgument_eq {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : 0 ≤ t) : smoothLogArgument ε t = t + ε := by
  have hδ : 0 < smoothLogDelta ε := by dsimp [smoothLogDelta]; positivity
  have hcδ : smoothLogC ε + 2 * smoothLogDelta ε = 0 := by
    dsimp [smoothLogC, smoothLogDelta]
    ring
  have htail : (∫ x in (0 : ℝ)..t,
      gStep (smoothLogC ε) (smoothLogDelta ε) x) = t := by
    rw [intervalIntegral.integral_of_le ht]
    rw [show (∫ x in Set.Ioc 0 t,
        gStep (smoothLogC ε) (smoothLogDelta ε) x) = ∫ x in Set.Ioc 0 t, (1 : ℝ) by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact gStep_eq_one hδ (by simpa only [hcδ] using hx.1.le)]
    simp [ht]
  have hsplit : GApprox (smoothLogC ε) (smoothLogDelta ε) t =
      GApprox (smoothLogC ε) (smoothLogDelta ε) 0 + t := by
    unfold GApprox
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (gStep_intervalIntegrable _ _ _ _) (gStep_intervalIntegrable _ _ _ _), htail]
  dsimp [smoothLogArgument, smoothLogB]
  rw [hsplit]
  ring

private theorem logExtension_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (logExtension ε) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞)
      (GApprox (smoothLogC ε) (smoothLogDelta ε)) :=
    Weighted.GApprox_contDiff_top _ _
  have hS : ContDiff ℝ (⊤ : ℕ∞) (smoothLogArgument ε) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => smoothLogB ε + GApprox (smoothLogC ε) (smoothLogDelta ε) x)
    exact contDiff_const.add hG
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (Real.log ∘ smoothLogArgument ε) Set.univ := by
    apply Real.contDiffOn_log.comp hS.contDiffOn
    intro t ht
    exact (smoothLogArgument_pos hε t).ne'
  exact contDiffOn_univ.mp (by simpa only [logExtension] using hcomp)

private theorem logExtension_deriv_formula (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    deriv (logExtension ε) t =
      gStep (smoothLogC ε) (smoothLogDelta ε) t / smoothLogArgument ε t := by
  have hS := smoothLogArgument_pos hε t
  have hcomp := (Real.hasDerivAt_log hS.ne').comp t
    ((GApprox_hasDerivAt (smoothLogC ε) (smoothLogDelta ε) t).const_add
      (smoothLogB ε))
  change deriv (Real.log ∘ smoothLogArgument ε) t = _
  have h := hcomp.deriv
  simpa [smoothLogArgument, div_eq_mul_inv, mul_comm] using h

private theorem logExtension_deriv_bound (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    |deriv (logExtension ε) t| ≤ 3 / (2 * ε) := by
  have hSpos := smoothLogArgument_pos hε t
  have hSlow := smoothLogB_lower hε
  have hstep0 := gStep_nonneg (smoothLogC ε) (smoothLogDelta ε) t
  have hstep1 := gStep_le_one (smoothLogC ε) (smoothLogDelta ε) t
  have hden : 2 * ε / 3 ≤ smoothLogArgument ε t := by
    have hδ : 0 < smoothLogDelta ε := by dsimp [smoothLogDelta]; positivity
    have hG := gApprox_nonneg hδ (c := smoothLogC ε) (t := t)
    dsimp [smoothLogArgument]
    linarith
  rw [logExtension_deriv_formula ε hε t, abs_div, abs_of_nonneg hstep0,
    abs_of_pos hSpos]
  calc
    gStep (smoothLogC ε) (smoothLogDelta ε) t / smoothLogArgument ε t ≤
        1 / smoothLogArgument ε t :=
      div_le_div_of_nonneg_right hstep1 (le_of_lt hSpos)
    _ ≤ 1 / (2 * ε / 3) := one_div_le_one_div_of_le (by positivity) hden
    _ = 3 / (2 * ε) := by field_simp

private theorem logExtension_agrees (ε : ℝ) (hε : 0 < ε) {t : ℝ}
    (ht : 0 ≤ t) : logExtension ε t = Real.log (t + ε) := by
  rw [logExtension, Function.comp_apply, smoothLogArgument_eq hε ht]

private theorem logExtension_deriv_agrees (ε : ℝ) (hε : 0 < ε) {t : ℝ}
    (ht : 0 ≤ t) : deriv (logExtension ε) t = (t + ε)⁻¹ := by
  have hδ : 0 < smoothLogDelta ε := by dsimp [smoothLogDelta]; positivity
  have hcδ : smoothLogC ε + 2 * smoothLogDelta ε = 0 := by
    dsimp [smoothLogC, smoothLogDelta]
    ring
  rw [logExtension_deriv_formula ε hε t,
    gStep_eq_one hδ (by simpa only [hcδ] using ht), smoothLogArgument_eq hε ht]
  simp [div_eq_mul_inv]

/-- For a nonnegative supersolution `u` on the unit cube and `ε > 0`, `log (u + ε)` belongs
to the weighted space with gradient `(u + ε)⁻¹ G`. -/
theorem log_memH1a {d : ℕ} (hd : 3 ≤ d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSupersolution a (originCube 1) u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
    (ε : ℝ) (hε : 0 < ε) :
    MemH1a a (originCube 1) (fun x => Real.log (u x + ε))
      (fun x => (u x + ε)⁻¹ • G x) := by
  have hneZero : NeZero d := ⟨by omega⟩
  let := hneZero
  have hcube : originCube 1 = auxCube 1 (fun _ : Fin d => 0) := by
    ext x
    simp [originCube, auxCube, sub_self, sub_zero, Int.cast_zero,
      zero_mul, abs_lt]
  have hV : IsOpenBoundedConvexDomain (originCube (d := d) 1) := by
    rw [hcube]
    exact LowerFractional.auxCube_isOpenBoundedConvexDomain (d := d) 1 (fun _ => 0)
  have hne : (originCube (d := d) 1).Nonempty := by
    rw [hcube]
    exact LowerFractional.auxCube_nonempty (d := d) 1 (fun _ => 0)
  have hsub : IsWeightedSubsolution a (originCube 1) (-u) (-G) := by
    change IsWeightedSubsolution a (originCube 1) (fun x => -u x) (fun x => -G x)
    exact hu
  have hmem : MemH1a a (originCube 1) u G :=
    by simpa only [Pi.neg_apply, neg_neg] using Weighted.MemH1a.neg hV hne ha hsub.1
  have hcomp := Weighted.MemH1a.comp hV hne ha hmem
    (Φ := logExtension ε) (logExtension_smooth ε hε)
    (L := ⟨3 / (2 * ε), by positivity⟩)
    (fun t => logExtension_deriv_bound ε hε t)
  refine Weighted.MemH1a.congr_ae hcomp ?_ ?_
  · filter_upwards [hnonneg] with x hx
    exact logExtension_agrees ε hε hx
  · filter_upwards [hnonneg] with x hx
    rw [logExtension_deriv_agrees ε hε hx]

end
end CoarseDeGiorgi.Harnack.Log
