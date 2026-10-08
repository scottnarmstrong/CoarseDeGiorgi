import CoarseDeGiorgi.Weighted.UpperResponse

/-! # Cellwise harmonic replacement for the Whitney lift

The seed's eventual affine-cell and geometric properties are separate inputs.
This module uses the proved weighted Dirichlet replacement and response, without
importing any of the main-result statement files.
-/

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Adding a constant to the function of a `MemH1a` pair keeps it a `MemH1a` pair. -/
lemma lift_memH1a_add_const (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G) (c : ℝ) : MemH1a a V (fun x => u x + c) G := by
  have hc : IsSmoothCore a V (fun _ => c) := by
    refine ⟨contDiffOn_const, ?_, ?_⟩
    · exact (continuous_const.continuousOn.integrableOn_compact
        hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
    · simp [weightedEnergy, smoothGrad, vecDot]
  have hgc : smoothGrad (fun _ : Vec d => c) = fun _ => (0 : Vec d) := by
    funext x i
    simp [smoothGrad]
  have hm := Weighted.memH1a_of_isSmoothCore hV.isOpen ha hc
  change MemH1a a V (fun _ => c) (smoothGrad (fun _ => c)) at hm
  rw [hgc] at hm
  have hs := Weighted.MemH1a.add hV hne ha hu hm
  change MemH1a a V (fun x => u x + c) (G + fun _ => 0) at hs
  simpa only [show (fun _ : Vec d => (0 : Vec d)) = (0 : Vec d → Vec d) from rfl, add_zero] using hs

/-- A chosen harmonic representative of an affine datum, retaining the literal gradient. -/
def liftCellPair (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) : (Vec d → ℝ) × (Vec d → Vec d) :=
  ⟨Classical.choose (Weighted.harmonic_replacement hV hne ha
      (Weighted.responseAffine_memH1a hV ha e)),
    Classical.choose (Classical.choose_spec (Weighted.harmonic_replacement hV hne ha
      (Weighted.responseAffine_memH1a hV ha e)))⟩

lemma liftCellPair_spec (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    IsWeightedSolution a V (liftCellPair hV hne ha e).1 (liftCellPair hV hne ha e).2 ∧
    MemH1a0 a V ((liftCellPair hV hne ha e).1 - Weighted.responseAffine e)
      ((liftCellPair hV hne ha e).2 - fun _ => e) := by
  have hh := Classical.choose_spec (Classical.choose_spec (Weighted.harmonic_replacement hV hne ha
    (Weighted.responseAffine_memH1a hV ha e)))
  exact ⟨hh.1, hh.2.1⟩

/-- The affine harmonic cell energy is the literal directional response times cell volume. -/
lemma liftCellPair_energy (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    weightedEnergy a V (liftCellPair hV hne ha e).2 =
      volume V * ENNReal.ofReal (upperDirectionalResponseSol a V e).toReal := by
  obtain ⟨hh, hb⟩ := liftCellPair_spec hV hne ha e
  have hp := Weighted.upperHarmonicLinear_eq hV hne ha e hh hb
  have hresp := Weighted.upper_response_eq_norm hV hne ha e
  rw [hresp, EReal.toReal_coe]
  have hv : 0 < (volume V).toReal := by
    exact ENNReal.toReal_pos (hV.isOpen.measure_pos volume hne).ne'
      hV.isBoundedDomain.isBounded.measure_lt_top.ne
  have hn : weightedEnergy a V (liftCellPair hV hne ha e).2 =
      ENNReal.ofReal (‖Weighted.upperHarmonicLinear hV hne ha e‖ ^ 2) := by
    rw [hp, UniformSpace.Completion.norm_coe]
    exact Weighted.GradientCore.energy_eq_norm_sq ha (Weighted.memH1aEnergyField hV.isOpen ha hh.1)
  rw [hn]
  calc
    _ = ENNReal.ofReal ((volume V).toReal *
        ((volume V).toReal⁻¹ * ‖Weighted.upperHarmonicLinear hV hne ha e‖ ^ 2)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
    _ = _ := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hV.isBoundedDomain.isBounded.measure_lt_top.ne]


/-- Orthogonality gives the exact seed/correction energy splitting on each cell. -/
lemma liftCellPair_correction_energy (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    weightedEnergy a V (fun _ => e) =
      weightedEnergy a V (liftCellPair hV hne ha e).2 +
      weightedEnergy a V ((liftCellPair hV hne ha e).2 - fun _ => e) := by
  obtain ⟨hh, hb⟩ := liftCellPair_spec hV hne ha e
  have hn := Weighted.MemH1a0.neg hV hne ha hb
  have hcomp : MemH1a0 a V (Weighted.responseAffine e - (liftCellPair hV hne ha e).1)
      ((fun _ => e) - (liftCellPair hV hne ha e).2) := by
    simpa only [neg_sub] using hn
  have he := Weighted.IsWeightedSolution.energy_identity hV hne ha hh hcomp
  dsimp only [Weighted.weightedEnergy] at he
  rw [he, ← neg_sub ((liftCellPair hV hne ha e).2) (fun _ => e)]
  exact congrArg (fun z => weightedEnergy a V (liftCellPair hV hne ha e).2 + z)
    (Weighted.energy_neg ((liftCellPair hV hne ha e).2 - fun _ => e))

/-- Constant offsets in affine seed data preserve the harmonic gradient and boundary correction. -/
lemma liftCellPair_add_const (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ) :
    IsWeightedSolution a V (fun x => (liftCellPair hV hne ha e).1 x + c)
      (liftCellPair hV hne ha e).2 ∧
    MemH1a0 a V ((fun x => (liftCellPair hV hne ha e).1 x + c) -
        (fun x => Weighted.responseAffine e x + c))
      ((liftCellPair hV hne ha e).2 - fun _ => e) := by
  obtain ⟨hh, hb⟩ := liftCellPair_spec hV hne ha e
  constructor
  · exact ⟨lift_memH1a_add_const hV hne ha hh.1 c, hh.2⟩
  · convert hb using 1
    funext x
    simp only [Pi.sub_apply]
    ring

end
end CoarseDeGiorgi.Whitney
