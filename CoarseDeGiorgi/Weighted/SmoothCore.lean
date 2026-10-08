import CoarseDeGiorgi.Weighted.Energy
import Homogenization.Sobolev.W1p.BasicLemmas

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The classical gradient of a smooth-on-open-set function is measurable. -/
theorem smoothGrad_aestronglyMeasurable (hV : IsOpen V)
    {f : Vec d → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) :
    AEStronglyMeasurable (smoothGrad f) (volume.restrict V) := by
  apply ContinuousOn.aestronglyMeasurable _ hV.measurableSet
  apply continuousOn_pi.mpr
  intro i
  exact (hf.continuousOn_fderiv_of_isOpen hV (by simp)).clm_apply continuousOn_const

/-- A continuous-on-domain factor times a supported continuous test is integrable globally. -/
theorem integrable_mul_supported {f ψ : Vec d → ℝ}
    (hf : ContinuousOn f V) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ V) : Integrable (fun x => f x * ψ x) volume := by
  have hi : IntegrableOn (fun x => f x * ψ x) (tsupport ψ) :=
    ((hf.mono hs).mul hψ.continuousOn).integrableOn_compact hc.isCompact
  rw [← integrableOn_univ]
  exact hi.of_forall_sdiff_eq_zero MeasurableSet.univ (by
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport hx.2, mul_zero])

/-- Smoothness on the open domain suffices for the classical weak-gradient identity. -/
theorem hasWeakGradientOn_of_contDiffOn (hV : IsOpen V)
    {f : Vec d → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) :
    HasWeakGradientOn V f (smoothGrad f) := by
  intro i ψ hψ hc hs
  have hfc := hf.continuousOn
  have hdfc : ContinuousOn (fun x => fderiv ℝ f x (basisVec i)) V :=
    (hf.continuousOn_fderiv_of_isOpen hV (by simp)).clm_apply continuousOn_const
  have hdψc : Continuous (fun x => fderiv ℝ ψ x (basisVec i)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψs : tsupport (fun x => fderiv ℝ ψ x (basisVec i)) ⊆ tsupport ψ :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := ψ) (basisVec i))
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_supported hdfc hψ.continuous hc hs)
    (integrable_mul_supported hfc hdψc (hc.fderiv_apply (𝕜 := ℝ) (basisVec i)) (hdψs.trans hs))
    (integrable_mul_supported hfc hψ.continuous hc hs)
    (fun x hx => (hf.differentiableOn (by simp) x (hs hx)).differentiableAt (hV.mem_nhds (hs hx)))
    (fun x _ => (hψ.differentiable (by simp)).differentiableAt)
  change (∫ x in V, f x * fderiv ℝ ψ x (basisVec i)) =
    -(∫ x in V, fderiv ℝ f x (basisVec i) * ψ x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hibp
  · intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hdψs.trans hs h))
    rw [hz, mul_zero]


/-- Changing the gradient on a null set preserves the weak-gradient identity. -/
theorem hasWeakGradientOn_congr_grad {u : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : HasWeakGradientOn V u G) (heq : G =ᵐ[volume.restrict V] H) :
    HasWeakGradientOn V u H := by
  intro i ψ hψ hc hs
  rw [hu i ψ hψ hc hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

/-- Subtraction of classical gradients on an open smoothness domain. -/
theorem smoothGrad_sub_ae (hV : IsOpen V) {f g : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) :
    smoothGrad (f - g) =ᵐ[volume.restrict V] smoothGrad f - smoothGrad g := by
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  funext i
  change fderiv ℝ (f - g) x (basisVec i) = fderiv ℝ f x (basisVec i) - fderiv ℝ g x (basisVec i)
  rw [fderiv_sub ((hf.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx))
    ((hg.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx))]
  rfl

end CoarseDeGiorgi.Weighted
