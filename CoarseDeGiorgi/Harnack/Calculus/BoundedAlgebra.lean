import CoarseDeGiorgi.Weighted.Truncation.Chain
import CoarseDeGiorgi.Weighted.PairOperations
import CoarseDeGiorgi.Weighted.TestingCompactSupport
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.Support

namespace CoarseDeGiorgi.Harnack.Calculus

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A smooth function equal to `x ^ 2` (with derivative `2 * x`) on `[-B, B]`, with bounded
derivative. -/
private theorem exists_bounded_square_extension (B : ℝ) (hB : 0 ≤ B) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      (∀ x, |x| ≤ B → Φ x = x ^ 2 ∧ deriv Φ x = 2 * x) ∧
      ∃ L : ℝ≥0, ∀ x, |deriv Φ x| ≤ L := by
  let χ : ContDiffBump (0 : ℝ) := ⟨B + 1, B + 2, by linarith, by linarith⟩
  let Φ : ℝ → ℝ := fun x => χ x * x ^ 2
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ := χ.contDiff
  have hχdiff : Differentiable ℝ χ := hχsmooth.differentiable (by simp)
  have hΦsmooth : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    dsimp [Φ]
    fun_prop
  have hΦsupport : HasCompactSupport Φ := by
    dsimp [Φ]
    exact χ.hasCompactSupport.mul_right
  have hderivSupport : HasCompactSupport (deriv Φ) := hΦsupport.deriv
  have hDcont : Continuous (fun x => ‖deriv Φ x‖) :=
    (hΦsmooth.continuous_deriv (by simp)).norm
  obtain ⟨C, hC⟩ := hDcont.bddAbove_range_of_hasCompactSupport
    (hderivSupport.comp_left norm_zero)
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hL (x : ℝ) : |deriv Φ x| ≤ L := by
    have hx : ‖deriv Φ x‖ ≤ C := hC (Set.mem_range_self x)
    change |deriv Φ x| ≤ max C 0
    simpa only [Real.norm_eq_abs] using hx.trans (le_max_left _ _)
  refine ⟨Φ, hΦsmooth, ?_, L, hL⟩
  intro x hx
  have hball : x ∈ Metric.ball (0 : ℝ) (B + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    rw [Real.norm_eq_abs]
    linarith
  have hone : χ =ᶠ[𝓝 x] fun _ => 1 := χ.eventuallyEq_one_of_mem_ball hball
  have hχx : χ x = 1 := hone.eq_of_nhds
  have hχd : deriv χ x = 0 := by
    have hd := (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hone
    rw [hd.deriv]
  constructor
  · simp [Φ, hχx]
  · calc
      deriv Φ x = deriv χ x * x ^ 2 + χ x * (2 * x) := by
        change deriv (fun y : ℝ => χ y * y ^ 2) x = _
        rw [deriv_fun_mul (hχdiff x) (by fun_prop)]
        rw [deriv_pow_field 2]
        simp
      _ = 2 * x := by rw [hχd, hχx]; ring

/-- The product of two bounded `H¹_a` functions is in `H¹_a`, with the product-rule gradient
(bounded algebra property of `p.weighted.calculus`). -/
theorem MemH1a.mul_bounded [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f g : Vec d → ℝ} {F G : Vec d → Vec d}
    (hf : CoarseDeGiorgi.MemH1a a V f F)
    (hg : CoarseDeGiorgi.MemH1a a V g G)
    {Bf Bg : ℝ} (hfb : ∀ᵐ x ∂volume.restrict V, |f x| ≤ Bf)
    (hgb : ∀ᵐ x ∂volume.restrict V, |g x| ≤ Bg) :
    CoarseDeGiorgi.MemH1a a V (fun x => f x * g x)
      (fun x => f x • G x + g x • F x) := by
  let C : ℝ := |Bf| + |Bg|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hplusBound : ∀ᵐ x ∂volume.restrict V, |f x + g x| ≤ C := by
    filter_upwards [hfb, hgb] with x hfx hgx
    dsimp [C]
    calc
      |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ Bf + Bg := add_le_add hfx hgx
      _ ≤ |Bf| + |Bg| := add_le_add (le_abs_self _) (le_abs_self _)
  have hminusBound : ∀ᵐ x ∂volume.restrict V, |f x - g x| ≤ C := by
    filter_upwards [hfb, hgb] with x hfx hgx
    dsimp [C]
    calc
      |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
      _ ≤ Bf + Bg := add_le_add hfx hgx
      _ ≤ |Bf| + |Bg| := add_le_add (le_abs_self _) (le_abs_self _)
  obtain ⟨Φ, hΦ, hΦdata, _, hΦbound⟩ := exists_bounded_square_extension C hC
  let uPlus : Vec d → ℝ := f + g
  let uMinus : Vec d → ℝ := f - g
  let gradPlus : Vec d → Vec d := F + G
  let gradMinus : Vec d → Vec d := F - G
  have hPlus : CoarseDeGiorgi.MemH1a a V uPlus gradPlus := by
    exact CoarseDeGiorgi.Weighted.MemH1a.add hV hne ha hf hg
  have hMinus : CoarseDeGiorgi.MemH1a a V uMinus gradMinus := by
    exact CoarseDeGiorgi.Weighted.MemH1a.sub hV hne ha hf hg
  have hPlusSq := CoarseDeGiorgi.Weighted.MemH1a.comp hV hne ha hPlus hΦ hΦbound
  have hMinusSq := CoarseDeGiorgi.Weighted.MemH1a.comp hV hne ha hMinus hΦ hΦbound
  have hPlusVal : (fun x => Φ (uPlus x)) =ᵐ[volume.restrict V]
      (fun x => (f x + g x) ^ 2) := by
    filter_upwards [hplusBound] with x hx
    exact (hΦdata (f x + g x) (by simpa [uPlus] using hx)).1
  have hPlusGrad : (fun x => deriv Φ (uPlus x) • gradPlus x) =ᵐ[volume.restrict V]
      (fun x => (2 * (f x + g x)) • (F x + G x)) := by
    filter_upwards [hplusBound] with x hx
    have hspec := hΦdata (f x + g x) (by simpa [uPlus] using hx)
    simp only [uPlus, gradPlus, Pi.add_apply]
    rw [hspec.2]
  have hMinusVal : (fun x => Φ (uMinus x)) =ᵐ[volume.restrict V]
      (fun x => (f x - g x) ^ 2) := by
    filter_upwards [hminusBound] with x hx
    exact (hΦdata (f x - g x) (by simpa [uMinus] using hx)).1
  have hMinusGrad : (fun x => deriv Φ (uMinus x) • gradMinus x) =ᵐ[volume.restrict V]
      (fun x => (2 * (f x - g x)) • (F x - G x)) := by
    filter_upwards [hminusBound] with x hx
    have hspec := hΦdata (f x - g x) (by simpa [uMinus] using hx)
    simp only [uMinus, gradMinus, Pi.sub_apply]
    rw [hspec.2]
  have hPlusSq' : CoarseDeGiorgi.MemH1a a V (fun x => (f x + g x) ^ 2)
      (fun x => (2 * (f x + g x)) • (F x + G x)) := by
    exact CoarseDeGiorgi.Weighted.MemH1a.congr_ae hPlusSq
      (by simpa only [Function.comp_def] using hPlusVal) hPlusGrad
  have hMinusSq' : CoarseDeGiorgi.MemH1a a V (fun x => (f x - g x) ^ 2)
      (fun x => (2 * (f x - g x)) • (F x - G x)) := by
    exact CoarseDeGiorgi.Weighted.MemH1a.congr_ae hMinusSq
      (by simpa only [Function.comp_def] using hMinusVal) hMinusGrad
  have hDiff : CoarseDeGiorgi.MemH1a a V
      (fun x => (f x + g x) ^ 2 - (f x - g x) ^ 2)
      (fun x => (2 * (f x + g x)) • (F x + G x) -
        (2 * (f x - g x)) • (F x - G x)) :=
    CoarseDeGiorgi.Weighted.MemH1a.sub hV hne ha hPlusSq' hMinusSq'
  let scale : ℝ → ℝ := fun t => t / 4
  have hscale : ContDiff ℝ (⊤ : ℕ∞) scale := by fun_prop
  have hscaleBound : ∀ t, |deriv scale t| ≤ (1 : ℝ≥0) := by
    intro t
    simp [scale]
    norm_num
  have hProduct := CoarseDeGiorgi.Weighted.MemH1a.comp hV hne ha hDiff
    hscale hscaleBound
  have hproductValue : (fun x => scale ((f x + g x) ^ 2 - (f x - g x) ^ 2)) =ᵐ[
      volume.restrict V] (fun x => f x * g x) := by
    filter_upwards with x
    dsimp [scale]
    ring
  have hproductGrad : (fun x => deriv scale ((f x + g x) ^ 2 - (f x - g x) ^ 2) •
      ((2 * (f x + g x)) • (F x + G x) - (2 * (f x - g x)) • (F x - G x))) =ᵐ[
      volume.restrict V] (fun x => f x • G x + g x • F x) := by
    filter_upwards with x
    have hdscale : deriv scale ((f x + g x) ^ 2 - (f x - g x) ^ 2) = (1 / 4 : ℝ) := by
      simp [scale]
    rw [hdscale]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  exact CoarseDeGiorgi.Weighted.MemH1a.congr_ae hProduct hproductValue hproductGrad

end CoarseDeGiorgi.Harnack.Calculus
