module

public import CoarseDeGiorgi.LowerFractional.Restriction
public import CoarseDeGiorgi.Foundations.Reconstruction.Representatives

/-! Recover the actual gradient from the value equalities exported by lift
admissibility. The represented gradients are not assumed equal. -/

@[expose] public section

namespace CoarseDeGiorgi.Adapters

open Homogenization MeasureTheory Filter

variable {d : ℕ} [NeZero d] {a : CoeffField d} {V U : Set (Vec d)}

/-- AE equal values of represented weighted pairs have AE equal gradients
on every open convex subdomain. -/
theorem lift_testing_gradient_of_ae_value
    (hV : IsOpenBoundedConvexDomain V) (hneV : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (hU : IsOpenBoundedConvexDomain U)
    (hneU : U.Nonempty) (hUV : U ⊆ V)
    {ψ v : Vec d → ℝ} {J F : Vec d → Vec d}
    (hψ : MemH1a a V ψ J) (hv : MemH1a a U v F)
    (heq : ψ =ᵐ[volume.restrict U] v) : J =ᵐ[volume.restrict U] F := by
  have haU := LowerFractional.weightedCoeffOn_mono ha hUV
  have hψU := LowerFractional.memH1a_restrict hV hneV ha hU hUV hψ
  have hwψ := Weighted.memH1a_memW11 hU hneU haU hψU
  have hwv := Weighted.memH1a_memW11 hU hneU haU hv
  have hweak := Foundations.Reconstruction.hasWeakGradientOn_congr_ae heq
    EventuallyEq.rfl hwψ.2.2.1
  have hcoord : ∀ i : Fin d, (fun x => J x i) =ᵐ[volume.restrict U] (fun x => F x i) := by
    intro i
    apply HasWeakPartialDerivOn.ae_eq hU.isOpen _ _ (hweak i) (hwv.2.2.1 i)
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hwψ.2.1 i).locallyIntegrable
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hwv.2.1 i).locallyIntegrable
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  exact funext hx

end CoarseDeGiorgi.Adapters
