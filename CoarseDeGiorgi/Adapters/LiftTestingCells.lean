module

public import CoarseDeGiorgi.Whitney.LiftCell
public import CoarseDeGiorgi.Whitney.LiftZeroExtension
public import CoarseDeGiorgi.Adapters.LiftTestingGradient
public import CoarseDeGiorgi.Weighted.TestingCompactSupport
public import CoarseDeGiorgi.Weighted.Truncation.PositivePart
public import CoarseDeGiorgi.Weighted.ZeroCore

/-! Actual exterior gradients and energy contraction on the harmonic cells. -/

@[expose] public section

namespace CoarseDeGiorgi.Adapters

open Homogenization MeasureTheory Set Filter
open scoped ENNReal

variable {d : ℕ} [NeZero d] {a : CoeffField d} {V U : Set (Vec d)}

/-- Admissibility's cellwise value identity determines the represented gradient. -/
theorem lift_testing_harmonic_cell_gradient
    (hV : IsOpenBoundedConvexDomain V) (hneV : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (hU : IsOpenBoundedConvexDomain U)
    (hneU : U.Nonempty) (hUV : U ⊆ V) (e : Vec d) (c : ℝ)
    {ψ : Vec d → ℝ} {J : Vec d → Vec d} (hψ : MemH1a0 a V ψ J)
    (heq : ψ =ᵐ[volume.restrict U]
      (fun x => (Whitney.liftCellPair hU hneU (Whitney.lift_coeff_mono ha hUV) e).1 x + c)) :
    J =ᵐ[volume.restrict U]
      (Whitney.liftCellPair hU hneU (Whitney.lift_coeff_mono ha hUV) e).2 := by
  exact lift_testing_gradient_of_ae_value hV hneV ha hU hneU hUV (Weighted.MemH1a0.memH1a ha hψ)
    (Whitney.liftCellPair_add_const hU hneU (Whitney.lift_coeff_mono ha hUV) e c).1.1 heq

end CoarseDeGiorgi.Adapters
