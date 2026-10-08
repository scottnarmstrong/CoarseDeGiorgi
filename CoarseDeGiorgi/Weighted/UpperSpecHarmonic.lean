module

public import CoarseDeGiorgi.Weighted.UpperSpecDefs
public import CoarseDeGiorgi.Weighted.UpperResponseSupremum

@[expose] public section

namespace CoarseDeGiorgi.Weighted.UpperResponseImpl

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

theorem affine_add_const_gradient (e : Vec d) (c : ℝ) :
    smoothGrad (fun x => vecDot e x + c) = fun _ => e := by
  funext x i
  change fderiv ℝ (fun x => responseAffine e x + c) x (basisVec i) = e i
  rw [fderiv_add_const]
  exact congrFun (congrFun (smoothGrad_responseAffine e) x) i

theorem affine_add_const_mem (hV : IsOpenBoundedConvexDomain V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ) :
    MemH1a a V (fun x => vecDot e x + c) (fun _ => e) := by
  have hc : IsSmoothCore a V (fun x => vecDot e x + c) := by
    refine ⟨((responseAffine e).contDiff.add contDiff_const).contDiffOn, ?_, ?_⟩
    · exact (responseAffine_isSmoothCore hV ha e).2.1.add
        (integrableOn_const hV.isBoundedDomain.isBounded.measure_lt_top.ne)
    · change weightedEnergy a V (smoothGrad (fun x => vecDot e x + c)) < ⊤
      rw [affine_add_const_gradient]
      exact GradientCore.energy_lt_top ha (constantEnergyField ha e)
  simpa only [affine_add_const_gradient] using memH1a_of_isSmoothCore hV.isOpen ha hc

/-- Affine boundary harmonic replacement, including the zero dimensional case. -/
theorem upper_affine_replacement (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ) :
    ∃ h Gh, IsWeightedSolution a V h Gh ∧
      MemH1a0 a V (fun x => h x - (vecDot e x + c)) (fun x => Gh x - e) := by
  by_cases hd : d = 0
  · subst d
    have he : e = 0 := Subsingleton.elim _ _
    have hm : MemH1a a V (fun _ => c) (fun _ => 0) := by
      simpa [he, vecDot] using affine_add_const_mem hV ha e c
    have hs : IsWeightedSolution a V (fun _ => c) (fun _ => 0) := by
      apply isWeightedSolution_of_orthogonality hV.isOpen ha hm
      intro w H _
      simp [vecDot]
    refine ⟨fun _ => c, fun _ => 0, hs, ?_⟩
    have hz := memH1a0_of_supported hV.isOpen ha (φ := fun _ : Vec 0 => (0 : ℝ))
      contDiff_const (by simp [HasCompactSupport]) (by simp)
    have hg : smoothGrad (fun _ : Vec 0 => (0 : ℝ)) = fun _ => (0 : Vec 0) :=
      Subsingleton.elim _ _
    simpa [he, vecDot, hg] using hz
  · have : NeZero d := ⟨hd⟩
    obtain ⟨h, Gh, hh, hb, _⟩ := exists_harmonic_replacement hV hne ha
      (affine_add_const_mem hV ha e c)
    exact ⟨h, Gh, hh, hb⟩

/-- Projection identification uses the boundary gradient, allowing an arbitrary affine constant. -/
theorem upper_affine_gradient_eq [NeZero d] (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ)
    {h : Vec d → ℝ} {Gh : Vec d → Vec d} (hh : IsWeightedSolution a V h Gh)
    (hb : MemH1a0 a V (fun x => h x - (vecDot e x + c)) (fun x => Gh x - e)) :
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

/-- Every harmonic affine representative has the selected response energy. -/
theorem upper_affine_energy (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ)
    {h : Vec d → ℝ} {Gh : Vec d → Vec d} (hh : IsWeightedSolution a V h Gh)
    (hb : MemH1a0 a V (fun x => h x - (vecDot e x + c)) (fun x => Gh x - e)) :
    vecDot e (matVecMul (upperResponse a V hV hne ha) e) =
      volumeAverage V (fun x => vecDot (Gh x) (matVecMul (a x) (Gh x))) := by
  by_cases hd : d = 0
  · subst d
    simp [vecDot, volumeAverage]
  · have : NeZero d := ⟨hd⟩
    have he := upperResponse_directional hV hne ha e
    rw [upper_response_eq_norm hV hne ha e, upper_affine_gradient_eq hV hne ha e c hh hb,
      UniformSpace.Completion.norm_coe, GradientCore.norm_sq] at he
    change ((vecDot e (matVecMul (upperResponse a V hV hne ha) e) : ℝ) : EReal) =
      (((volume V).toReal⁻¹ * (weightedEnergy a V Gh).toReal : ℝ) : EReal) at he
    rw [energy_toReal ha hh.1.2.1] at he
    exact EReal.coe_eq_coe_iff.mp he


end CoarseDeGiorgi.Weighted.UpperResponseImpl
