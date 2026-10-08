import CoarseDeGiorgi.Whitney.Harmonic.Range
import CoarseDeGiorgi.Whitney.Harmonic.Geometry
import CoarseDeGiorgi.Whitney.SourceWitnessCorrection
import CoarseDeGiorgi.Adapters.LiftTestingCells
import CoarseDeGiorgi.Whitney.Interpolation.Exists

/-! Identification of the harmonic replacement on a cell with the library's affine cell pair. -/

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Any harmonic replacement of an affine datum is the library's cell pair plus the constant. -/
theorem cell_identification (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ) {L H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hL : ∀ x ∈ V, L x = Weighted.responseAffine e x + c)
    (hs : IsWeightedSolution a V H GH)
    (h0 : MemH1a0 a V (fun x => H x - L x) (fun x => GH x - e)) :
    (H =ᵐ[volume.restrict V] fun x => (Whitney.liftCellPair hV hne ha e).1 x + c) ∧
      GH =ᵐ[volume.restrict V] (Whitney.liftCellPair hV hne ha e).2 := by
  obtain ⟨hsol, hb⟩ := Whitney.liftCellPair_spec hV hne ha e
  have hk : IsWeightedSolution a V (fun x => (Whitney.liftCellPair hV hne ha e).1 x + c)
      (Whitney.liftCellPair hV hne ha e).2 :=
    Harnack.Calculus.IsWeightedSolution.addConst hV hne ha hsol c
  have hk0 : MemH1a0 a V (fun x => ((fun x => (Whitney.liftCellPair hV hne ha e).1 x + c) x) - L x)
      (fun x => (Whitney.liftCellPair hV hne ha e).2 x - e) := by
    refine memH1a0_congr_ae hb ?_ (Filter.EventuallyEq.rfl)
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    simp only [Pi.sub_apply, hL x hx]
    ring
  exact Weighted.harmonic_replacement_unique hV hne ha hs hk h0 hk0

end CoarseDeGiorgi.Whitney.Harmonic
