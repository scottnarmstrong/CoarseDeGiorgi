import CoarseDeGiorgi.Foundations.Reconstruction.Geometry
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Signed tests for the even-reflection construction

The finite sign sum uses the carrier's sup norm throughout. This file proves
smoothness, the coordinate chain rule, and cancellation on the lower face.
-/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Real reflection sign, indexed by a finite Boolean choice. -/
def reflectionSign (s : Bool) : ℝ := if s then 1 else -1

theorem reflectionSign_sq (s : Bool) : reflectionSign s * reflectionSign s = 1 := by
  cases s <;> norm_num [reflectionSign]

theorem reflectionSign_not (s : Bool) : reflectionSign (!s) = -reflectionSign s := by
  cases s <;> norm_num [reflectionSign]

/-- A diagonal sign map as a continuous linear map on the existing carrier. -/
def signLinear (s : Fin d → Bool) : Vec d →L[ℝ] Vec d :=
  ContinuousLinearMap.pi (fun i => reflectionSign (s i) • ContinuousLinearMap.proj i)

@[simp] theorem signLinear_apply (s : Fin d → Bool) (x : Vec d) (i : Fin d) :
    signLinear s x i = reflectionSign (s i) * x i := rfl

theorem signLinear_basisVec (s : Fin d → Bool) (i : Fin d) :
    signLinear s (basisVec i) = reflectionSign (s i) • basisVec i := by
  ext j
  simp only [signLinear_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply]
  by_cases h : j = i
  · subst j
    rfl
  · simp only [h, ite_false, mul_zero]

/-- Coordinate sign changes preserve the exact Euclidean length. -/
theorem euclidNorm_signLinear (s : Fin d → Bool) (x : Vec d) :
    euclidNorm (signLinear s x) = euclidNorm x := by
  unfold euclidNorm vecNormSq vecDot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [signLinear_apply]
  calc
    (reflectionSign (s i) * x i) * (reflectionSign (s i) * x i) =
        (reflectionSign (s i) * reflectionSign (s i)) * (x i * x i) := by ring
    _ = x i * x i := by rw [reflectionSign_sq, one_mul]

/-- The folded scalar test for the weak identity in coordinate `i`.
Its argument is relative to the lower corner of the original cube. -/
def foldedTest (i : Fin d) (φ : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ s : Fin d → Bool, reflectionSign (s i) * φ (signLinear s x)

theorem contDiff_foldedTest (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (foldedTest i φ) := by
  apply ContDiff.sum
  intro s _
  exact contDiff_const.mul (hφ.comp (signLinear s).contDiff)

/-- The sign in the test cancels the sign from differentiating the reflection map. -/
theorem fderiv_signed_test_basisVec (s : Fin d → Bool) (i : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    (fderiv ℝ (fun y => reflectionSign (s i) * φ (signLinear s y)) x) (basisVec i) =
      (fderiv ℝ φ (signLinear s x)) (basisVec i) := by
  have hφdiff := hφ.differentiable (by norm_num)
  have hd := ((hφdiff (signLinear s x)).hasFDerivAt.comp x
    (signLinear s).hasFDerivAt).const_mul (reflectionSign (s i))
  dsimp only [Function.comp_def] at hd
  rw [hd.fderiv, smul_apply, ContinuousLinearMap.comp_apply,
    signLinear_basisVec, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    reflectionSign_sq, one_mul]

theorem fderiv_foldedTest_basisVec (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    (fderiv ℝ (foldedTest i φ) x) (basisVec i) =
      ∑ s : Fin d → Bool, (fderiv ℝ φ (signLinear s x)) (basisVec i) := by
  unfold foldedTest
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro s _
    exact fderiv_signed_test_basisVec s i hφ x
  · intro s _
    exact (contDiff_const.mul (hφ.comp (signLinear s).contDiff)).differentiable
      (by norm_num) |>.differentiableAt

/-- Flipping one sign is an involution on the finite reflection choices. -/
def flipSign (i : Fin d) (s : Fin d → Bool) : Fin d → Bool :=
  Function.update s i (!s i)

theorem flipSign_involutive (i : Fin d) : Function.Involutive (flipSign i) := by
  intro s
  ext j
  by_cases h : j = i
  · subst j
    simp only [flipSign, Function.update_self, Bool.not_not]
  · simp only [flipSign, Function.update_of_ne h]

theorem flipSign_ne (i : Fin d) (s : Fin d → Bool) : flipSign i s ≠ s := by
  intro h
  have hi := congrFun h i
  simp only [flipSign, Function.update_self] at hi
  cases hs : s i <;> simp only [hs, Bool.not_false, Bool.not_true] at hi <;> cases hi

theorem signLinear_flipSign_of_eq_zero (i : Fin d) (s : Fin d → Bool) (x : Vec d)
    (hx : x i = 0) : signLinear (flipSign i s) x = signLinear s x := by
  ext j
  simp only [signLinear_apply, flipSign]
  by_cases h : j = i
  · subst j
    simp only [hx, mul_zero]
  · rw [Function.update_of_ne h]

/-- The folded test vanishes on the lower reflection face without any periodicity premise. -/
theorem foldedTest_eq_zero_of_lower_face (i : Fin d) (φ : Vec d → ℝ) (x : Vec d)
    (hx : x i = 0) : foldedTest i φ x = 0 := by
  classical
  unfold foldedTest
  apply Finset.sum_ninvolution (flipSign i)
  · intro s
    rw [signLinear_flipSign_of_eq_zero i s x hx]
    simp only [flipSign, Function.update_self, reflectionSign_not, neg_mul, add_neg_cancel]
  · intro s _
    exact flipSign_ne i s
  · intro s
    exact Finset.mem_univ _
  · exact flipSign_involutive i

/-- Flipping an upper-face sign changes the argument by exactly one signed period. -/
theorem signLinear_flipSign_upper_face (i : Fin d) (s : Fin d → Bool) (x : Vec d)
    {ℓ : ℝ} (hx : x i = ℓ) :
    signLinear s x = signLinear (flipSign i s) x +
      (2 * reflectionSign (s i) * ℓ) • basisVec i := by
  ext j
  simp only [signLinear_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply]
  by_cases h : j = i
  · subst j
    simp only [flipSign, Function.update_self, reflectionSign_not, hx, ite_true]
    ring
  · simp only [flipSign, Function.update_of_ne h, h, ite_false, mul_zero, add_zero]

/-- Periodicity makes the folded test vanish on the upper reflection face as well. -/
theorem foldedTest_eq_zero_of_upper_face (i : Fin d) (φ : Vec d → ℝ)
    {ℓ : ℝ} (hperiod : ∀ y, φ (y + (2 * ℓ) • basisVec i) = φ y)
    (x : Vec d) (hx : x i = ℓ) : foldedTest i φ x = 0 := by
  classical
  have hpair (s : Fin d → Bool) : φ (signLinear (flipSign i s) x) = φ (signLinear s x) := by
    cases hs : s i
    · have ht := signLinear_flipSign_upper_face i (flipSign i s) x hx
      rw [flipSign_involutive i s] at ht
      simp only [flipSign, Function.update_self, hs, Bool.not_false, reflectionSign,
        ite_true, mul_one] at ht
      simp only [flipSign, hs, Bool.not_false]
      rw [ht, hperiod]
    · have ht := signLinear_flipSign_upper_face i s x hx
      simp only [hs, reflectionSign, ite_true, mul_one] at ht
      rw [ht, hperiod]
  unfold foldedTest
  apply Finset.sum_ninvolution (flipSign i)
  · intro s
    rw [hpair s]
    simp only [flipSign, Function.update_self, reflectionSign_not, neg_mul, add_neg_cancel]
  · intro s _
    exact flipSign_ne i s
  · intro s
    exact Finset.mem_univ _
  · exact flipSign_involutive i

end

end CoarseDeGiorgi.Foundations.Reconstruction
