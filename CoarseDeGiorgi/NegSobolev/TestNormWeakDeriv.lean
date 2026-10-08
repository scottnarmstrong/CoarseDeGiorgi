import CoarseDeGiorgi.Statements.IsWeakDerivArray
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Integration by parts for smooth functions and ordered derivative arrays. -/


open Homogenization MeasureTheory
open scoped BigOperators

namespace CoarseDeGiorgi.NegSobolev

/-- Evaluation of a classical derivative at a fixed tuple is smooth. -/
theorem testNorm_contDiff_deriv_eval {d j : ℕ} {w : Vec d → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (v : Fin j → Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => iteratedFDeriv ℝ j w x v) := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec d) ℝ v).contDiff.comp
    (hw.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (by simp))

private theorem deriv_eval_tsupport {d j : ℕ} (w : Vec d → ℝ) (v : Fin j → Vec d) :
    tsupport (fun x => iteratedFDeriv ℝ j w x v) ⊆ tsupport w := by
  apply closure_minimal _ (isClosed_tsupport w)
  intro x hx
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) j
  intro hz
  exact hx (by change iteratedFDeriv ℝ j w x v = 0; rw [hz]; rfl)

private theorem integrable_mul_test {d : ℕ} {f ψ : Vec d → ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => f x * ψ x) volume :=
  (hf.mul hψ).integrable_of_hasCompactSupport (hc.mul_left)

/-- Moving an ordered tuple of derivatives off a compactly supported test reverses
its order on the smooth factor. No symmetry of higher derivatives is needed. -/
theorem testNorm_integral_iteratedFDeriv {d j : ℕ} {w φ : Vec d → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (v : Fin j → Vec d) :
    (∫ x, w x * iteratedFDeriv ℝ j φ x v) =
      (-1 : ℝ) ^ j * ∫ x, iteratedFDeriv ℝ j w x (fun k => v k.rev) * φ x := by
  induction j generalizing w with
  | zero => simp only [iteratedFDeriv_zero_apply, pow_zero, one_mul]
  | succ j ih =>
    let ψ : Vec d → ℝ := fun x => iteratedFDeriv ℝ j φ x (Fin.tail v)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := testNorm_contDiff_deriv_eval hφ _
    have hcψ : HasCompactSupport ψ :=
      hc.of_isClosed_subset (isClosed_tsupport ψ) (deriv_eval_tsupport φ _)
    have hdw : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ w x (v 0)) :=
      (hw.fderiv_right (by simp)).clm_apply contDiff_const
    have hdψ : Continuous (fun x => fderiv ℝ ψ x (v 0)) :=
      (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.clm_apply continuous_const
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_mul_test hdw.continuous hψ.continuous hcψ)
      (integrable_mul_test hw.continuous hdψ (hcψ.fderiv_apply (𝕜 := ℝ) (v 0)))
      (integrable_mul_test hw.continuous hψ.continuous hcψ)
      (fun _ _ => (hw.differentiable (by simp)).differentiableAt)
      (fun _ _ => (hψ.differentiable (by simp)).differentiableAt)
    have hleft (x : Vec d) : iteratedFDeriv ℝ (j + 1) φ x v =
        fderiv ℝ ψ x (v 0) :=
      (hφ.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast (ENat.natCast_lt_top j))).differentiableAt.iteratedFDeriv_succ_apply_left'
    have hright (x : Vec d) :
        iteratedFDeriv ℝ j (fun x => fderiv ℝ w x (v 0)) x
            (fun k => Fin.tail v k.rev) =
          iteratedFDeriv ℝ (j + 1) w x (fun k => v k.rev) := by
      rw [iteratedFDeriv_succ_apply_right,
        iteratedFDeriv_clm_apply_const_apply (hw.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (by simp)]
      congr 2
      · funext k
        simp only [Fin.tail, Fin.init, Fin.rev_castSucc]
      · simp only [Fin.rev_last]
    simp_rw [hleft]
    rw [hibp, ih hdw (Fin.tail v)]
    simp_rw [hright]
    rw [pow_succ]
    ring

/-- The reversed classical derivative tuple is a weak derivative array. Since all
ordered tuples are included, reversal only permutes the array entries. -/
theorem testNorm_isWeakDerivArray {d : ℕ} (U : Set (Vec d)) (j : ℕ)
    {w : Vec d → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    IsWeakDerivArray U j w
      (fun ι x => iteratedFDeriv ℝ j w x (fun k => basisVec (ι k.rev))) := by
  refine ⟨hw.continuous.locallyIntegrable.locallyIntegrableOn U, fun ι => ⟨?_, ?_⟩⟩
  · exact (testNorm_contDiff_deriv_eval hw _).continuous.locallyIntegrable.locallyIntegrableOn U
  · intro φ hφ hc hs
    have hdφs := (deriv_eval_tsupport φ (fun k => basisVec (ι k))).trans hs
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact testNorm_integral_iteratedFDeriv hw hφ hc _
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hdφs h)), mul_zero]

end CoarseDeGiorgi.NegSobolev
