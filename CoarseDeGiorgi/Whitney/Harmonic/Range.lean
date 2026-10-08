module

public import CoarseDeGiorgi.Whitney.Harmonic.Linear
public import CoarseDeGiorgi.Whitney.LiftRange
public import CoarseDeGiorgi.Harnack.Calculus.Supersolution

/-! Range preservation of the cellwise harmonic replacement of an affine datum. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Lower bound: a harmonic replacement of an affine datum with values `≥ m` is `≥ m`. -/
theorem replacement_lower (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (c m : ℝ) {L H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hL : ∀ x ∈ V, L x = Weighted.responseAffine e x + c)
    (hs : IsWeightedSolution a V H GH)
    (h0 : MemH1a0 a V (fun x => H x - L x) (fun x => GH x - e))
    (hm : ∀ x ∈ V, m ≤ L x) :
    ∀ᵐ x ∂volume.restrict V, m ≤ H x := by
  obtain ⟨hsol, hb⟩ := Whitney.liftCellPair_spec hV hne ha e
  have hr := Whitney.liftCellPair_range_nonneg hV hne ha e (c - m) (fun x hx => by
    have := hm x hx
    rw [hL x hx] at this
    linarith)
  have hk : IsWeightedSolution a V (fun x => (Whitney.liftCellPair hV hne ha e).1 x + c)
      (Whitney.liftCellPair hV hne ha e).2 :=
    Harnack.Calculus.IsWeightedSolution.addConst hV hne ha hsol c
  have hk0 : MemH1a0 a V (fun x => ((fun x => (Whitney.liftCellPair hV hne ha e).1 x + c) x) - L x)
      (fun x => (Whitney.liftCellPair hV hne ha e).2 x - e) := by
    refine memH1a0_congr_ae hb ?_ (Filter.EventuallyEq.rfl)
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    simp only [Pi.sub_apply, hL x hx]
    ring
  have hu := Weighted.harmonic_replacement_unique hV hne ha hs hk h0 hk0
  filter_upwards [hr, hu.1] with x hx hxe
  rw [hxe]
  linarith

/-- Two-sided range preservation. -/
theorem replacement_range (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (c m M : ℝ) {L H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hL : ∀ x ∈ V, L x = Weighted.responseAffine e x + c)
    (hs : IsWeightedSolution a V H GH)
    (h0 : MemH1a0 a V (fun x => H x - L x) (fun x => GH x - e))
    (hm : ∀ x ∈ V, m ≤ L x ∧ L x ≤ M) :
    ∀ᵐ x ∂volume.restrict V, m ≤ H x ∧ H x ≤ M := by
  have h1 := replacement_lower hV hne ha e c m hL hs h0 (fun x hx => (hm x hx).1)
  have hs' : IsWeightedSolution a V ((-1 : ℝ) • H) ((-1 : ℝ) • GH) := solution_smul hV hne ha hs (-1)
  have h0' : MemH1a0 a V (fun x => ((-1 : ℝ) • H) x - (fun x => -L x) x)
      (fun x => ((-1 : ℝ) • GH) x - -e) := by
    have := memH1a0_smul hV hne ha h0 (-1)
    refine memH1a0_congr_ae this ?_ ?_
    · exact Filter.Eventually.of_forall fun x => by simp; ring
    · exact Filter.Eventually.of_forall fun x => by
        simp only [Pi.smul_apply, smul_sub, neg_smul, one_smul]
  have h2 := replacement_lower hV hne ha (-e) (-c) (-M) (L := fun x => -L x)
    (H := (-1 : ℝ) • H) (GH := (-1 : ℝ) • GH)
    (fun x hx => by
      have : Weighted.responseAffine (-e) x = -Weighted.responseAffine e x := by
        change vecDot (-e) x = -vecDot e x
        simp [vecDot_neg_left]
      rw [this, hL x hx]; ring) hs' h0' (fun x hx => by linarith [(hm x hx).2])
  filter_upwards [h1, h2] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul] at hx2
  linarith

end CoarseDeGiorgi.Whitney.Harmonic
