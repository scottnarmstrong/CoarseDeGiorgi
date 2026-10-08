module

public import CoarseDeGiorgi.Weighted.HarmonicCore
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Lax–Milgram on the energy carrier supplies the boundary correction. -/
theorem exists_zero_correction (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (F : GradientCore ha) :
    ∃ z : zeroSubmodule hV.isOpen ha,
      ∀ y : zeroSubmodule hV.isOpen ha, inner ℝ y.val ((F : GradientHilbert ha) + z.val) = 0 := by
  let Z := zeroSubmodule hV.isOpen ha
  have : CompleteSpace Z := zeroHilbert_complete hV hne ha
  let B : Z →L[ℝ] Z →L[ℝ] ℝ := innerSL ℝ
  have hc : IsCoercive B := by
    refine ⟨1, zero_lt_one, fun z => ?_⟩
    change 1 * ‖z‖ * ‖z‖ ≤ inner ℝ z z
    rw [real_inner_self_eq_norm_sq]
    simp only [one_mul, pow_two, le_refl]
  let L : Z →L[ℝ] ℝ := -((innerSL ℝ (F : GradientHilbert ha)).comp Z.subtypeL)
  let z : Z := hc.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ Z).symm L)
  have hz (y : Z) : inner ℝ z y = -inner ℝ (F : GradientHilbert ha) y.val := by
    have h := hc.continuousLinearEquivOfBilin_apply z y
    rw [show hc.continuousLinearEquivOfBilin z = (InnerProductSpace.toDual ℝ Z).symm L by
      exact hc.continuousLinearEquivOfBilin.apply_symm_apply _] at h
    rw [InnerProductSpace.toDual_symm_apply] at h
    exact h.symm
  refine ⟨z, fun y => ?_⟩
  rw [inner_add_right, real_inner_comm (F : GradientHilbert ha) y.val,
    real_inner_comm z.val y.val]
  change inner ℝ (F : GradientHilbert ha) y.val + inner ℝ z y = 0
  rw [hz, add_neg_cancel]

/-- Harmonic replacement of a literal weighted Sobolev pair. -/
theorem exists_harmonic_replacement (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {g : Vec d → ℝ} {Gg : Vec d → Vec d}
    (hg : MemH1a a V g Gg) :
    ∃ h : Vec d → ℝ, ∃ Gh : Vec d → Vec d,
      CoarseDeGiorgi.IsWeightedSolution a V h Gh ∧
      MemH1a0 a V (h - g) (Gh - Gg) ∧
      ∀ w H, MemH1a0 a V w H →
        IntegrableOn (fun x => vecDot (H x) (matVecMul (a x) (Gh x))) V ∧
        (∫ x in V, vecDot (H x) (matVecMul (a x) (Gh x))) = 0 := by
  let F := memH1aEnergyField hV.isOpen ha hg
  obtain ⟨z, hz⟩ := exists_zero_correction hV hne ha F
  obtain ⟨u, hu⟩ := zeroHilbert_exists_rep hV hne ha z
  let K := gradientHilbertRep ha z.val
  have hfull := hg.add hV hne ha (hu.memH1a ha)
  have horth (w : Vec d → ℝ) (H : Vec d → Vec d) (hw : MemH1a0 a V w H) :
      (∫ x in V, vecDot (H x) (matVecMul (a x) ((Gg + K.field) x))) = 0 := by
    let W := memH1aEnergyField hV.isOpen ha (hw.memH1a ha)
    let y : zeroSubmodule hV.isOpen ha := ⟨(W : GradientHilbert ha), hw.gradient_mem hV hne ha⟩
    have h := hz y
    rw [← gradientHilbertRep_coe ha z.val, ← UniformSpace.Completion.coe_add,
      gradientHilbert_inner_coe] at h
    exact h
  have hsol := isWeightedSolution_of_orthogonality hV.isOpen ha hfull horth
  refine ⟨g + u, Gg + K.field, hsol, ?_, ?_⟩
  · simpa only [show g + u - g = u by abel, show Gg + K.field - Gg = K.field by abel] using hu
  · intro w H hw
    exact IsWeightedSolution.orthogonality hV hne ha hsol hw

end CoarseDeGiorgi.Weighted
