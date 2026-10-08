import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessProfileU
import CoarseDeGiorgi.SharpnessExamples.ScalarFluxLipschitz
import CoarseDeGiorgi.SharpnessExamples.ScalarTest

/-! # The flux `H(|x|²) x` and the sign of its pairing with test functions -/

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The flux `H(|x|²) x`. -/
def whF (d : ℕ) (ε : ℝ) (x : Vec d) : Vec d := fun i => whH d ε (vecNormSq x) * x i

theorem vecNormSq_eq_sum {d : ℕ} (x : Vec d) : vecNormSq x = ∑ i, x i ^ 2 := by
  unfold vecNormSq vecDot
  exact Finset.sum_congr rfl (fun i _ => (sq (x i)).symm)

theorem contDiff_vecNormSq {d : ℕ} : ContDiff ℝ ∞ (fun x : Vec d => vecNormSq x) := by
  simp only [vecNormSq_eq_sum]
  fun_prop

theorem vecNormSq_add_line {d : ℕ} (x : Vec d) (i : Fin d) (τ : ℝ) :
    vecNormSq (x + τ • basisVec i) = vecNormSq x + 2 * τ * x i + τ ^ 2 := by
  rw [vecNormSq_eq_sum, vecNormSq_eq_sum]
  have : ∀ j, (x + τ • basisVec i) j ^ 2 = x j ^ 2 + (if j = i then 2 * τ * x j + τ ^ 2 else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [basisVec]; ring
    · simp [basisVec, hj]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
  simp
  ring

theorem hasDerivAt_vecNormSq_line {d : ℕ} (x : Vec d) (i : Fin d) :
    HasDerivAt (fun τ : ℝ => vecNormSq (x + τ • basisVec i)) (2 * x i) 0 := by
  have : (fun τ : ℝ => vecNormSq (x + τ • basisVec i)) =
      fun τ => vecNormSq x + 2 * τ * x i + τ ^ 2 := funext (vecNormSq_add_line x i)
  rw [this]
  have h1 : HasDerivAt (fun τ : ℝ => 2 * τ * x i) (2 * x i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (x i)
  have h2 : HasDerivAt (fun τ : ℝ => τ ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have h3 := ((hasDerivAt_const (0 : ℝ) (vecNormSq x)).add h1).add h2
  convert h3 using 1
  simp

theorem contDiff_whF {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    ContDiff ℝ ∞ (fun x : Vec d => whF d ε x i) := by
  unfold whF
  exact ((contDiff_whH d hε).comp contDiff_vecNormSq).mul (contDiff_apply ℝ ℝ i)

theorem hasLineDerivAt_whF {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec d) (i : Fin d) :
    HasLineDerivAt ℝ (fun y : Vec d => whF d ε y i)
      (whH d ε (vecNormSq x) + 2 * x i ^ 2 * deriv (whH d ε) (vecNormSq x)) x (basisVec i) := by
  have hs := hasDerivAt_vecNormSq_line x i
  have hH : HasDerivAt (whH d ε) (deriv (whH d ε) (vecNormSq x)) (vecNormSq (x + (0 : ℝ) • basisVec i)) := by
    simp only [zero_smul, add_zero]
    exact ((contDiff_whH d hε).differentiable (by simp) _).hasDerivAt
  have hc := hH.comp 0 hs
  have hx : HasDerivAt (fun τ : ℝ => x i + τ) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x i)
  have hm := hc.mul hx
  unfold HasLineDerivAt
  convert hm using 1
  · funext τ
    simp [whF, Function.comp_def]
  · simp
    ring

theorem sum_lineDeriv_whF {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    ∑ i : Fin d, lineDeriv ℝ (fun y => whF d ε y i) x (basisVec i) =
      (d : ℝ) * whH d ε (vecNormSq x) + 2 * vecNormSq x * deriv (whH d ε) (vecNormSq x) := by
  have h : ∀ i, lineDeriv ℝ (fun y => whF d ε y i) x (basisVec i) =
      whH d ε (vecNormSq x) + 2 * x i ^ 2 * deriv (whH d ε) (vecNormSq x) :=
    fun i => (hasLineDerivAt_whF hε x i).lineDeriv
  simp_rw [h]
  rw [Finset.sum_add_distrib, vecNormSq_eq_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The pairing of `H(|x|²) x` with a nonnegative smooth test function is nonpositive. -/
theorem whFlux_test_nonpos {d : ℕ} [NeZero d] {ε : ℝ} (hε : 0 < ε)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ originCube 1) (hn : ∀ x, 0 ≤ φ x) :
    Integrable (fun x => vecDot (smoothGrad φ x) (whF d ε x)) volume ∧
    (∫ x, vecDot (smoothGrad φ x) (whF d ε x) ∂volume) ≤ 0 := by
  classical
  let L := fun i (x : Vec d) => fderiv ℝ φ x (basisVec i) * whF d ε x i
  let R := fun i (x : Vec d) => φ x * lineDeriv ℝ (fun y => whF d ε y i) x (basisVec i)
  have hi : ∀ i : Fin d, Integrable (L i) volume ∧ Integrable (R i) volume ∧
      (∫ x, L i x ∂volume) = -(∫ x, R i x ∂volume) := by
    intro i
    obtain ⟨K, hK⟩ := contDiff_exists_lipschitzOn_cube
      ((contDiff_whF hε i).of_le (by exact_mod_cast le_top))
    exact integral_test_mul_lipschitzOn_flux (by rw [originCube_eq_ball]; exact Metric.isOpen_ball)
      hφ hc hs hK (basisVec i)
  have hiL : Integrable (fun x => ∑ i : Fin d, L i x) volume := by
    have h := integrable_finsetSum Finset.univ (fun i _ => (hi i).1)
    simpa only [Finset.sum_fn] using h
  have heq : (fun x => vecDot (smoothGrad φ x) (whF d ε x)) = fun x => ∑ i : Fin d, L i x := rfl
  have hIBP : (∫ x, ∑ i : Fin d, L i x ∂volume) =
      -(∫ x, ∑ i : Fin d, R i x ∂volume) := by
    rw [integral_finsetSum _ (fun i _ => (hi i).1), integral_finsetSum _ (fun i _ => (hi i).2.1)]
    simp_rw [(hi _).2.2]
    simp only [Finset.sum_neg_distrib]
  have hnonneg : 0 ≤ ∫ x, ∑ i : Fin d, R i x ∂volume := by
    apply integral_nonneg
    intro x
    change 0 ≤ ∑ i : Fin d, φ x * lineDeriv ℝ (fun y => whF d ε y i) x (basisVec i)
    rw [← Finset.mul_sum, sum_lineDeriv_whF hε]
    exact mul_nonneg (hn x) (whH_div_nonneg d hε _)
  refine ⟨?_, ?_⟩
  · rwa [← heq] at hiL
  · rw [heq, hIBP]
    exact neg_nonpos.mpr hnonneg

end

end CoarseDeGiorgi.SharpnessExamples
