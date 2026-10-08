import CoarseDeGiorgi.Weighted.LowerSpecDefs

namespace CoarseDeGiorgi.Weighted.LowerResponseImpl

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

theorem lowerResponseInv_riesz [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    vecDot e (matVecMul (lowerResponseInv a V hV hne ha) e) =
      (volume V).toReal⁻¹ * ‖lowerResponseGradient hV.isOpen ha e‖ ^ 2 :=
  EReal.coe_injective ((lowerResponseInv_directional hV hne ha e).trans
    (lowerDirectionalResponse_eq_riesz hV hne ha e))

/-- The supremum over all weighted functions equals the harmonic supremum. -/
theorem lowerResponseInv_all_functions
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    ((vecDot e (matVecMul (lowerResponseInv a V hV hne ha) e) : ℝ) : EReal) =
      ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d) (_ : MemH1a a V w G),
        ((volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
          2 * vecDot e (G x)) : ℝ) : EReal) := by
  rw [lowerResponseInv_directional]
  apply le_antisymm
  · unfold lowerDirectionalResponse
    refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
    exact le_iSup_of_le w (le_iSup_of_le G (le_iSup_of_le hw.1 le_rfl))
  · cases d with
    | zero =>
      rw [lowerDirectionalResponse_dim_zero]
      refine iSup_le fun w => iSup_le fun G => iSup_le fun _ => ?_
      simp [vecDot, volumeAverage]
    | succ n =>
      rw [lowerDirectionalResponse_eq_riesz hV hne ha e]
      refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
      exact EReal.coe_le_coe (lower_integrand_le hV hne ha e hw)

/-- A globally integrable mean-zero weighted solution attains the supremum. -/
theorem lowerResponseInv_attained
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    ∃ w : Vec d → ℝ, ∃ G : Vec d → Vec d,
      IsWeightedSolution a V w G ∧ IntegrableOn w V ∧ volumeAverage V w = 0 ∧
      ((volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
        2 * vecDot e (G x)) : ℝ) : EReal) =
        ((vecDot e (matVecMul (lowerResponseInv a V hV hne ha) e) : ℝ) : EReal) := by
  cases d with
  | zero =>
    refine ⟨0, 0, lower_zero_solution a V, integrableOn_zero, ?_, ?_⟩
    · simp [volumeAverage]
    · simp [vecDot, volumeAverage]
  | succ n =>
    obtain ⟨u, hu, hm⟩ := exists_lowerRiesz_solution hV hne ha e
    let U := gradientHilbertRep ha (lowerRiesz hV.isOpen ha e).val.snd
    have hU : (memH1aEnergyField hV.isOpen ha hu.1 : GradientHilbert ha) =
        (lowerRiesz hV.isOpen ha e).val.snd := by
      calc
        (memH1aEnergyField hV.isOpen ha hu.1 : GradientHilbert ha) =
            (U : GradientHilbert ha) :=
          (GradientCore.coe_eq_iff ha _ _).mpr Filter.EventuallyEq.rfl
        _ = _ := gradientHilbertRep_coe ha _
    refine ⟨u, U.field, hu, (memH1a_memW11 hV hne ha hu.1).1, hm, ?_⟩
    apply congrArg (fun r : ℝ => (r : EReal))
    rw [lower_integrand_eq hV hne ha e hu.1, hU, sub_self, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, lowerResponseInv_riesz]
    rfl


end CoarseDeGiorgi.Weighted.LowerResponseImpl
