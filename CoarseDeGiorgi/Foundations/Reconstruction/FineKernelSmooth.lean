import CoarseDeGiorgi.Foundations.Reconstruction.SmoothParameterIntegral

/-! # Infinite spatial smoothness of the fine kernels -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- A smooth time cutoff equal to one on the integration interval after scaling. -/
def kernelTimeBump : ContDiffBump (2 : ℝ) where
  rIn := 1
  rOut := 3 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Cut off the irrelevant singularity at time zero. -/
def patchedFineIntegrand (h : ℝ) (p : ℝ × Vec d) : Vec d :=
  kernelTimeBump (p.1 / h) • fineKernelIntegrand p.1 p.2

theorem patchedFineIntegrand_eq {h t : ℝ} (hh : 0 < h) (ht : t ∈ Set.Icc h (3 * h))
    (v : Vec d) : patchedFineIntegrand h (t, v) = fineKernelIntegrand t v := by
  have hone : kernelTimeBump (t / h) = 1 := by
    apply kernelTimeBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -(1 : ℝ) ≤ t / h - 2 ∧ t / h - 2 ≤ 1
    have hlo : 1 ≤ t / h := (le_div_iff₀ hh).mpr (by simpa using ht.1)
    have hhi : t / h ≤ 3 := (div_le_iff₀ hh).mpr ht.2
    constructor <;> linarith
  simp only [patchedFineIntegrand, hone, one_smul]

/-- The time cutoff removes the only singularity of the jointly smooth integrand. -/
theorem contDiff_patchedFineIntegrand (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (patchedFineIntegrand (d := d) h) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases ht : p.1 = 0
  · have heq : patchedFineIntegrand h =ᶠ[𝓝 p] fun _ => (0 : Vec d) := by
      have hsmall : ∀ᶠ q : ℝ × Vec d in 𝓝 p, |q.1 / h| < 1 / 4 := by
        have hc : ContinuousAt (fun q : ℝ × Vec d => |q.1 / h|) p :=
          (continuous_fst.div_const h).abs.continuousAt
        exact hc.eventually (gt_mem_nhds (by simp [ht]))
      filter_upwards [hsmall] with q hq
      have hz : kernelTimeBump (q.1 / h) = 0 := by
        apply kernelTimeBump.zero_of_le_dist
        rw [Real.dist_eq, abs_of_nonpos (by linarith [le_abs_self (q.1 / h)])]
        change 3 / 2 ≤ _
        linarith [le_abs_self (q.1 / h)]
      simp only [patchedFineIntegrand, hz, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec d => q.1⁻¹) p :=
      contDiffAt_fst.inv ht
    have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec d => scaledRho q.1 q.2) p :=
      (contDiffAt_fst.pow d).inv (pow_ne_zero _ ht) |>.mul
        (contDiff_reconstructionRho.contDiffAt.comp p (hinv.smul contDiffAt_snd))
    have hi : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec d => fineKernelIntegrand q.1 q.2) p :=
      hr.smul (hinv.smul contDiffAt_snd)
    exact (kernelTimeBump.contDiff.comp (contDiff_fst.div_const h)).contDiffAt.smul hi

/-- The Euclidean precursor of every fine kernel is C∞. -/
theorem contDiff_fineKernel {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (fineKernel (d := d) h) := by
  have heq : fineKernel (d := d) h =
      fun v => ∫ t in Set.Icc h (3 * h), patchedFineIntegrand h (t, v) ∂volume := by
    funext v
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    exact (patchedFineIntegrand_eq hh ht v).symm
  rw [heq]
  apply contDiff_infty.mpr
  intro n
  exact contDiff_integral_Icc_joint n _ ((contDiff_patchedFineIntegrand h).of_le (by simp)) h (3 * h)

end

end CoarseDeGiorgi.Foundations.Reconstruction
