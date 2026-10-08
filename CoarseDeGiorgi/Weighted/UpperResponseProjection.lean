import CoarseDeGiorgi.Weighted.UpperResponseAffine

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Harmonic affine gradients depend linearly on their direction. -/
noncomputable def upperHarmonicLinear (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) :
    Vec d →ₗ[ℝ] GradientHilbert ha := by
  have : CompleteSpace (zeroSubmodule hV.isOpen ha) := zeroHilbert_complete hV hne ha
  exact ((ContinuousLinearMap.id ℝ (GradientHilbert ha) -
    (zeroSubmodule hV.isOpen ha).starProjection).toLinearMap).comp
    ((UniformSpace.Completion.toComplL.toLinearMap).comp (constantEnergyLinear ha))

theorem upperHarmonicLinear_eq (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d)
    {h : Vec d → ℝ} {Gh : Vec d → Vec d}
    (hh : CoarseDeGiorgi.IsWeightedSolution a V h Gh)
    (hb : MemH1a0 a V (h - responseAffine e) (Gh - fun _ => e)) :
    upperHarmonicLinear hV hne ha e =
      (memH1aEnergyField hV.isOpen ha hh.1 : GradientHilbert ha) := by
  have : CompleteSpace (zeroSubmodule hV.isOpen ha) := zeroHilbert_complete hV hne ha
  let Z := zeroSubmodule hV.isOpen ha
  let F := constantEnergyField ha e
  let H := memH1aEnergyField hV.isOpen ha hh.1
  have hdiff : (F : GradientHilbert ha) - (H : GradientHilbert ha) ∈ Z := by
    have hm := Z.neg_mem (hb.gradient_mem hV hne ha)
    convert hm using 1
    rw [← UniformSpace.Completion.coe_sub, ← UniformSpace.Completion.coe_neg]
    congr 1
    apply Subtype.ext
    funext x
    change e - Gh x = -(Gh x - e)
    abel
  have hp : Z.starProjection (F : GradientHilbert ha) =
      (F : GradientHilbert ha) - (H : GradientHilbert ha) := by
    apply Z.eq_starProjection_of_mem_of_inner_eq_zero hdiff
    intro y hy
    obtain ⟨u, hu⟩ := zeroHilbert_exists_rep hV hne ha ⟨y, hy⟩
    have hi := (IsWeightedSolution.orthogonality hV hne ha hh hu).2
    rw [show (F : GradientHilbert ha) - ((F : GradientHilbert ha) - H) = H by abel]
    rw [real_inner_comm, ← gradientHilbertRep_coe ha y, gradientHilbert_inner_coe]
    exact hi
  change (F : GradientHilbert ha) - Z.starProjection (F : GradientHilbert ha) = H
  rw [hp]
  abel

/-- The linear Hilbert map has a literal harmonic representative with affine boundary data. -/
theorem upperHarmonicLinear_exists_rep (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    ∃ h Gh, ∃ hh : CoarseDeGiorgi.IsWeightedSolution a V h Gh,
      MemH1a0 a V (h - responseAffine e) (Gh - fun _ => e) ∧
      upperHarmonicLinear hV hne ha e =
        (memH1aEnergyField hV.isOpen ha hh.1 :
          GradientHilbert ha) := by
  obtain ⟨h, Gh, hh, hb, _⟩ := exists_harmonic_replacement hV hne ha
    (responseAffine_memH1a hV ha e)
  exact ⟨h, Gh, hh, hb, upperHarmonicLinear_eq hV hne ha e hh hb⟩

end CoarseDeGiorgi.Weighted
