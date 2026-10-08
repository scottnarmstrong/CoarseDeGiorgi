module

public import CoarseDeGiorgi.NegSobolev.TestNormSmooth
public import CoarseDeGiorgi.Foundations.Euclid.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! The Gaussian derivative convolution difference estimate, split at square-root time. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Topology

namespace CoarseDeGiorgi.NegSobolev

theorem testNorm_gaussDeriv_kernel_difference (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) (z : Vec d),
      Foundations.Euclid.eNorm2 z ≤ Real.sqrt t → ∀ x : Vec d,
      |gaussDerivEntry t ht ι (x + z) - gaussDerivEntry t ht ι x| ≤
        (C * t ^ (-(((j + 1 : ℕ) : ℝ) / 2)) * Foundations.Euclid.eNorm2 z) *
          gaussianKernel (2 * (2 * t)) (by positivity) x := by
  obtain ⟨C, hC, hbound⟩ := gaussDerivEntry_fderiv_bound d j
  let B := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C * B, mul_pos hC hB, fun t ht ι z hz x => ?_⟩
  have hrad : Real.sqrt t < Real.sqrt (2 * t) := Real.sqrt_lt_sqrt ht.le (by linarith)
  have hx : x ∈ Metric.ball x (Real.sqrt (2 * t)) := Metric.mem_ball_self (by positivity)
  have hxz : x + z ∈ Metric.ball x (Real.sqrt (2 * t)) := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (Foundations.Euclid.norm_le_eNorm2 z).trans_lt (hz.trans_lt hrad)
  have hd : ∀ u ∈ Metric.ball x (Real.sqrt (2 * t)),
      DifferentiableAt ℝ (gaussDerivEntry t ht ι) u :=
    fun u _ => ((gaussDerivEntry_contDiff t ht ι).differentiable (by norm_num)).differentiableAt
  let A := C * t ^ (-(((j + 1 : ℕ) : ℝ) / 2))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : ∀ u ∈ Metric.ball x (Real.sqrt (2 * t)),
      ‖fderiv ℝ (gaussDerivEntry t ht ι) u‖ ≤
        A * B * gaussianKernel (2 * (2 * t)) (by positivity) x := by
    intro u hu
    have hc := gaussDeriv_gaussian_local (2 * t) (by positivity) u x 0
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hu)
    simp only [sub_zero] at hc
    exact (hbound t ht ι u).trans (by
      simpa only [A, B, mul_assoc] using mul_le_mul_of_nonneg_left hc hA)
  have hmv := (convex_ball x (Real.sqrt (2 * t))).norm_image_sub_le_of_norm_fderiv_le
    hd hb hx hxz
  rw [Real.norm_eq_abs, add_sub_cancel_left] at hmv
  calc
    _ ≤ A * B * gaussianKernel (2 * (2 * t)) (by positivity) x * ‖z‖ := hmv
    _ ≤ A * B * gaussianKernel (2 * (2 * t)) (by positivity) x * Foundations.Euclid.eNorm2 z :=
      mul_le_mul_of_nonneg_left (Foundations.Euclid.norm_le_eNorm2 z)
        (mul_nonneg (mul_nonneg hA hB.le) (gaussianKernel_nonneg _ _ _))
    _ = _ := by dsimp [A]; ring

theorem testNorm_gaussDeriv_translation_bound (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (_hr : 1 < r) (g : Vec d → ℝ),
      MemLp g (ENNReal.ofReal r) volume → ∀ (t : ℝ) (ht : 0 < t)
        (ι : Fin j → Fin d) (z : Vec d),
      eLpNorm (fun x => (∫ y, gaussDerivEntry t ht ι (x + z - y) * g y) -
        (∫ y, gaussDerivEntry t ht ι (x - y) * g y)) (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal (min 1 (Foundations.Euclid.eNorm2 z / Real.sqrt t)) *
            (ENNReal.ofReal (C * t ^ (-((j : ℝ) / 2))) * eLpNorm g (ENNReal.ofReal r) volume) := by
  obtain ⟨C₀, hC₀, hnorm⟩ := testNorm_gaussDeriv_eLpNorm_bound d j
  obtain ⟨C₁, hC₁, hdiff⟩ := testNorm_gaussDeriv_kernel_difference d j
  let C := 2 * C₀ + C₁
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun r hr g hg t ht ι z => ?_⟩
  let F := fun x => ∫ y, gaussDerivEntry t ht ι (x - y) * g y
  have hm : AEStronglyMeasurable F volume :=
    (testNorm_gaussDeriv_contDiff r hr g hg t ht ι).continuous.aestronglyMeasurable
  have hscale : 0 ≤ t ^ (-((j : ℝ) / 2)) := Real.rpow_nonneg ht.le _
  by_cases hz : Foundations.Euclid.eNorm2 z ≤ Real.sqrt t
  · have hratio : Foundations.Euclid.eNorm2 z / Real.sqrt t ≤ 1 :=
      (div_le_one (Real.sqrt_pos.mpr ht)).mpr hz
    rw [min_eq_right hratio]
    let K := fun x => gaussDerivEntry t ht ι (x + z) - gaussDerivEntry t ht ι x
    have hK : AEStronglyMeasurable K volume :=
      (((gaussDerivEntry_contDiff t ht ι).continuous.comp (by fun_prop)).sub
        (gaussDerivEntry_contDiff t ht ι).continuous).aestronglyMeasurable
    have heq : (fun x => F (x + z) - F x) = fun x => ∫ y, K (x - y) * g y := by
      funext x
      dsimp only [F]
      rw [← integral_sub]
      · congr 1
        funext y
        dsimp [K]
        rw [sub_mul]
        congr 2
        abel_nf
      · exact testNorm_convolution_integrable r hr
          (gaussDeriv_memLp_iterated t ht ι _ (Real.HolderConjugate.conjExponent hr).symm.pos) hg (x + z)
      · exact testNorm_convolution_integrable r hr
          (gaussDeriv_memLp_iterated t ht ι _ (Real.HolderConjugate.conjExponent hr).symm.pos) hg x
    change eLpNorm (fun x => F (x + z) - F x) _ _ ≤ _
    rw [heq]
    have h := testNorm_convolution_eLpNorm_le_gaussian r hr hK hg
      (C₁ * t ^ (-(((j + 1 : ℕ) : ℝ) / 2)) * Foundations.Euclid.eNorm2 z)
      (2 * (2 * t)) (mul_nonneg (mul_nonneg hC₁.le (Real.rpow_nonneg ht.le _))
        (Foundations.Euclid.eNorm2_nonneg z))
      (by positivity) (hdiff t ht ι z hz)
    have hpow : t ^ (-(((j + 1 : ℕ) : ℝ) / 2)) = t ^ (-((j : ℝ) / 2)) / Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht]
      congr 1
      push_cast
      ring
    rw [hpow] at h
    refine h.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (Foundations.Euclid.eNorm2_nonneg z) (Real.sqrt_nonneg t))]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hc : C₁ ≤ C := by dsimp [C]; linarith
    have hz0 := Foundations.Euclid.eNorm2_nonneg z
    calc
      _ = (Foundations.Euclid.eNorm2 z / Real.sqrt t) * (C₁ * t ^ (-((j : ℝ) / 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hscale) (by positivity)
  · have hratio : 1 ≤ Foundations.Euclid.eNorm2 z / Real.sqrt t :=
      (one_le_div (Real.sqrt_pos.mpr ht)).mpr (le_of_not_ge hz)
    rw [min_eq_left hratio, ENNReal.ofReal_one, one_mul]
    change eLpNorm (fun x => F (x + z) - F x) _ _ ≤ _
    have hmp := measurePreserving_add_right (volume : Measure (Vec d)) z
    have htr : eLpNorm (fun x => F (x + z)) (ENNReal.ofReal r) volume =
        eLpNorm F (ENNReal.ofReal r) volume := eLpNorm_comp_measurePreserving hm hmp
    refine (eLpNorm_sub_le (by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr.le)).trans ?_
    rw [htr]
    have hb := hnorm r hr g hg t ht ι
    refine (add_le_add hb hb).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hc : C₀ + C₀ ≤ C := by dsimp [C]; linarith
    simpa only [← add_mul] using mul_le_mul_of_nonneg_right hc hscale

end CoarseDeGiorgi.NegSobolev
