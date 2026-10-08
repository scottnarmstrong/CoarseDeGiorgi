import CoarseDeGiorgi.Weighted.UpperResponseSupremum
import CoarseDeGiorgi.Weighted.UpperResponseMatrix

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Affine boundary data fix the average of the harmonic gradient. -/
theorem upper_harmonic_integral (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d)
    {h : Vec d → ℝ} {Gh : Vec d → Vec d}
    (hh : CoarseDeGiorgi.IsWeightedSolution a V h Gh)
    (hb : MemH1a0 a V (h - responseAffine e) (Gh - fun _ => e)) :
    (∫ x in V, Gh x) = (volume V).toReal • e := by
  obtain ⟨_, _, hc⟩ := exists_memH1a0_coercivity hV hne
  have hi := (hc a ha _ _ hb).2.1
  have hG : IntegrableOn Gh V :=
    Integrable.of_eval (memH1a_memW11 hV hne ha hh.1).2.1
  have hconst : IntegrableOn (fun _ : Vec d => e) V :=
    integrableOn_const hV.isBoundedDomain.isBounded.measure_lt_top.ne
  change (∫ x in V, Gh x - e) = 0 at hi
  rw [integral_sub hG hconst, integral_const] at hi
  simpa only [Measure.real, Measure.restrict_apply_univ] using sub_eq_zero.mp hi

/-- The linear harmonic-gradient map has no kernel. -/
theorem upperHarmonicLinear_ne_zero (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) {e : Vec d} (he : e ≠ 0) :
    upperHarmonicLinear hV hne ha e ≠ 0 := by
  intro hz
  obtain ⟨h, Gh, hh, hb, heq⟩ := upperHarmonicLinear_exists_rep hV hne ha e
  let H := memH1aEnergyField hV.isOpen ha hh.1
  have hcoe : (H : GradientHilbert ha) = (0 : GradientCore ha) := by
    simpa only [UniformSpace.Completion.coe_zero] using heq.symm.trans hz
  have hAE : Gh =ᵐ[volume.restrict V] (0 : Vec d → Vec d) :=
    (GradientCore.coe_eq_iff ha H 0).mp hcoe
  have hint : (∫ x in V, Gh x) = 0 := by
    rw [integral_congr_ae hAE]
    simp
  have hvol : (volume V).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hV.isOpen.measure_pos volume hne).ne'
      hV.isBoundedDomain.isBounded.measure_lt_top.ne).ne'
  have hi := upper_harmonic_integral hV hne ha e hh hb
  rw [hint] at hi
  exact he ((smul_eq_zero.mp hi.symm).resolve_left hvol)

/-- The normalized energy bilinear form of harmonic affine gradients. -/
noncomputable def upperResponseBilin (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) : LinearMap.BilinForm ℝ (Vec d) :=
  (volume V).toReal⁻¹ • (innerₗ (GradientHilbert ha)).compl₁₂
    (upperHarmonicLinear hV hne ha) (upperHarmonicLinear hV hne ha)

theorem upperResponseBilin_apply (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e f : Vec d) :
    upperResponseBilin hV hne ha e f = (volume V).toReal⁻¹ *
      inner ℝ (upperHarmonicLinear hV hne ha e) (upperHarmonicLinear hV hne ha f) := rfl

theorem upperResponseBilin_symm (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) :
    (upperResponseBilin hV hne ha).IsSymm := by
  constructor
  intro e f
  simp only [upperResponseBilin_apply, real_inner_comm]

theorem upperResponseBilin_pos (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) (he : e ≠ 0) :
    0 < upperResponseBilin hV hne ha e e := by
  rw [upperResponseBilin_apply, real_inner_self_eq_norm_sq]
  apply mul_pos
  · exact inv_pos.mpr (ENNReal.toReal_pos (hV.isOpen.measure_pos volume hne).ne'
      hV.isBoundedDomain.isBounded.measure_lt_top.ne)
  · exact sq_pos_of_pos (norm_pos_iff.mpr (upperHarmonicLinear_ne_zero hV hne ha he))

/-- Upper-response matrix existence and uniqueness in positive dimension. -/
theorem upperResponse_existsUnique_of_neZero (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) :
    ∃! A : Mat d, A.PosDef ∧ ∀ e : Vec d,
      ((vecDot e (matVecMul A e) : ℝ) : EReal) =
        CoarseDeGiorgi.upperDirectionalResponseSol a V e := by
  obtain ⟨A, hA, huniq⟩ := existsUnique_posDef_matrix_of_bilin
    (upperResponseBilin hV hne ha) (upperResponseBilin_symm hV hne ha)
    (upperResponseBilin_pos hV hne ha)
  have response (e : Vec d) : CoarseDeGiorgi.upperDirectionalResponseSol a V e =
      ((upperResponseBilin hV hne ha e e : ℝ) : EReal) := by
    rw [upperResponseBilin_apply, real_inner_self_eq_norm_sq, upper_response_eq_norm hV hne ha]
  refine ⟨A, ⟨hA.1, fun e => ?_⟩, fun M hM => ?_⟩
  · rw [hA.2 e, response e]
  · apply huniq M
    exact ⟨hM.1, fun e => EReal.coe_eq_coe_iff.mp ((hM.2 e).trans (response e))⟩

end CoarseDeGiorgi.Weighted
