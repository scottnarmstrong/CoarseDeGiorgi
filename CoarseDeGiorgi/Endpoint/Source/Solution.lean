module

public import CoarseDeGiorgi.Endpoint.Source.Order
public import CoarseDeGiorgi.LowerFractional.Restriction
public import CoarseDeGiorgi.Statements.IsWeightedSolution

/-! Restriction of a pair that annihilates tests supported in a subdomain gives a solution there. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

theorem smoothGrad_eq_zero_of_notMem {φ : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport φ) :
    CoarseDeGiorgi.smoothGrad φ x = 0 := by
  funext i
  simp [CoarseDeGiorgi.smoothGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

theorem isWeightedSolution_of_vanishing [NeZero d] (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) {Q : Set (Vec d)}
    (hQ : IsOpenBoundedConvexDomain Q) (hQV : Q ⊆ V) {w : Vec d → ℝ} {X : Vec d → Vec d}
    (hw : CoarseDeGiorgi.MemH1a a V w X)
    (hvan : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Q → fluxPairing a V X φ = 0) :
    CoarseDeGiorgi.IsWeightedSolution a Q w X := by
  refine ⟨CoarseDeGiorgi.LowerFractional.memH1a_restrict hV hne ha hQ hQV hw, ?_⟩
  intro φ hφ hc hs
  refine ⟨?_, ?_⟩
  · exact (fluxPairing_integrable hV.isOpen ha hw.2.1 (MemH1a.energy_lt_top hV.isOpen ha hw)
      hφ hc (hs.trans hQV)).mono_set hQV
  · have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
      (f := fun x => vecDot (CoarseDeGiorgi.smoothGrad φ x) (matVecMul (a x) (X x)))
      hV.isOpen.measurableSet hQV (fun x hx => by
        rw [smoothGrad_eq_zero_of_notMem (fun h' => hx.2 (hs h'))]
        simp [vecDot])
    rw [← h]
    exact hvan φ hφ hc hs

end CoarseDeGiorgi.Endpoint
