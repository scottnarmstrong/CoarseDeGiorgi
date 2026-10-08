module

public import CoarseDeGiorgi.Weighted.UpperResponseProjection
public import CoarseDeGiorgi.Statements.UpperDirectionalResponseSol

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

omit [NeZero d] in
/-- The source objective is an integrable energy pairing for every admissible pair. -/
theorem upper_objective_eq (hV : IsOpenBoundedConvexDomain V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : CoarseDeGiorgi.IsWeightedSolution a V w G) :
    volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
      2 * vecDot e (matVecMul (a x) (G x))) =
    (volume V).toReal⁻¹ *
      (-‖(memH1aEnergyField hV.isOpen ha hw.1 : GradientHilbert ha)‖ ^ 2 +
        2 * inner ℝ (constantEnergyField ha e : GradientHilbert ha)
          (memH1aEnergyField hV.isOpen ha hw.1 : GradientHilbert ha)) := by
  let W := memH1aEnergyField hV.isOpen ha hw.1
  let F := constantEnergyField ha e
  have hq := GradientCore.quadratic_integrable ha W
  have hp := (pairing_integrable_and_bound ha (GradientCore.measurable ha F)
    (GradientCore.measurable ha W) (GradientCore.energy_lt_top ha F)
    (GradientCore.energy_lt_top ha W)).1
  change IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) V at hq
  change IntegrableOn (fun x => vecDot e (matVecMul (a x) (G x))) V at hp
  change (volume V).toReal⁻¹ * (∫ x in V, -vecDot (G x) (matVecMul (a x) (G x)) +
    2 * vecDot e (matVecMul (a x) (G x))) = _
  rw [integral_add (f := fun x => -vecDot (G x) (matVecMul (a x) (G x)))
    (g := fun x => 2 * vecDot e (matVecMul (a x) (G x))) hq.neg (hp.const_mul 2),
    integral_neg, integral_const_mul,
    gradientHilbert_inner_coe, UniformSpace.Completion.norm_coe,
    GradientCore.norm_sq, energy_toReal ha (GradientCore.measurable ha W)]
  rfl

/-- Harmonic affine replacement gives the literal EReal supremum, with attainment. -/
theorem upper_response_eq_norm (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    CoarseDeGiorgi.upperDirectionalResponseSol a V e =
      (((volume V).toReal⁻¹ * ‖upperHarmonicLinear hV hne ha e‖ ^ 2 : ℝ) : EReal) := by
  obtain ⟨h, Gh, hh, hb, he⟩ := upperHarmonicLinear_exists_rep hV hne ha e
  let H := memH1aEnergyField hV.isOpen ha hh.1
  let F := constantEnergyField ha e
  have pairing (w : Vec d → ℝ) (G : Vec d → Vec d)
      (hw : CoarseDeGiorgi.IsWeightedSolution a V w G) :
      inner ℝ (F : GradientHilbert ha)
        (memH1aEnergyField hV.isOpen ha hw.1 : GradientHilbert ha) =
      inner ℝ (H : GradientHilbert ha)
        (memH1aEnergyField hV.isOpen ha hw.1 : GradientHilbert ha) := by
    let W := memH1aEnergyField hV.isOpen ha hw.1
    have hz := (IsWeightedSolution.orthogonality hV hne ha hw hb).2
    have hcore : memH1aEnergyField hV.isOpen ha (hb.memH1a ha) = H - F := by
      apply Subtype.ext
      rfl
    have hi : inner ℝ ((H : GradientHilbert ha) - F) (W : GradientHilbert ha) = 0 := by
      rw [← UniformSpace.Completion.coe_sub, ← hcore, gradientHilbert_inner_coe]
      exact hz
    rw [inner_sub_left] at hi
    exact (sub_eq_zero.mp hi).symm
  have obj (w : Vec d → ℝ) (G : Vec d → Vec d)
      (hw : CoarseDeGiorgi.IsWeightedSolution a V w G) :
      volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
        2 * vecDot e (matVecMul (a x) (G x))) ≤
      (volume V).toReal⁻¹ * ‖upperHarmonicLinear hV hne ha e‖ ^ 2 := by
    rw [upper_objective_eq hV ha e hw, pairing w G hw, he]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
    have hi := norm_sub_sq_real (H : GradientHilbert ha)
      (memH1aEnergyField hV.isOpen ha hw.1 : GradientHilbert ha)
    nlinarith only [hi, sq_nonneg
      ‖(H : GradientHilbert ha) - (memH1aEnergyField hV.isOpen ha hw.1 : GradientHilbert ha)‖]
  have attained : volumeAverage V
      (fun x => -vecDot (Gh x) (matVecMul (a x) (Gh x)) +
        2 * vecDot e (matVecMul (a x) (Gh x))) =
      (volume V).toReal⁻¹ * ‖upperHarmonicLinear hV hne ha e‖ ^ 2 := by
    rw [upper_objective_eq hV ha e hh, pairing h Gh hh, he,
      real_inner_self_eq_norm_sq]
    ring
  unfold CoarseDeGiorgi.upperDirectionalResponseSol
  apply le_antisymm
  · refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
    exact EReal.coe_le_coe_iff.mpr (obj w G hw)
  · rw [← attained]
    exact le_iSup_of_le h (le_iSup_of_le Gh (le_iSup_of_le hh le_rfl))

end CoarseDeGiorgi.Weighted
