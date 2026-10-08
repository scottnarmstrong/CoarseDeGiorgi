module

public import CoarseDeGiorgi.Endpoint.Capacitary.Affine
public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import CoarseDeGiorgi.Whitney.LiftSums
public import CoarseDeGiorgi.Whitney.LiftZeroExtension
public import CoarseDeGiorgi.Statements.UpperResponseSpec
public import CoarseDeGiorgi.Statements.UpperResponseOnCell

/-! A finite cellwise harmonic replacement of the capacitary seed. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Set
open CoarseDeGiorgi.Whitney
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ} [NeZero d]

/-- A zero-direction cell representative vanishes almost everywhere. -/
theorem capacitary_liftCellPair_zero {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) {a : CoeffField d} (ha : IsWeightedCoeffOn U a) :
    (liftCellPair hU hne ha 0).1 =ᵐ[volume.restrict U] 0 := by
  have hz : MemH1a0 a U (0 : Vec d → ℝ) (0 : Vec d → Vec d) := by
    have h := Weighted.memH1a0_of_supported hU.isOpen ha
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (0 : Vec d → ℝ))
      HasCompactSupport.zero (by
        change tsupport (0 : Vec d → ℝ) ⊆ U
        rw [tsupport_zero]
        exact empty_subset U)
    have hg : smoothGrad (0 : Vec d → ℝ) = (0 : Vec d → Vec d) := by
      funext x i
      simp [smoothGrad]
    change MemH1a0 a U (0 : Vec d → ℝ) (smoothGrad (0 : Vec d → ℝ)) at h
    rw [hg] at h
    exact h
  have hs : IsWeightedSolution a U (0 : Vec d → ℝ) (0 : Vec d → Vec d) := by
    refine ⟨Weighted.MemH1a0.memH1a ha hz, ?_⟩
    intro φ _ _ _
    simp only [Pi.zero_apply, matVecMul_zero, vecDot_zero_right]
    exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
  have hb : MemH1a0 a U ((0 : Vec d → ℝ) - Weighted.responseAffine (0 : Vec d))
      ((0 : Vec d → Vec d) - fun _ => (0 : Vec d)) := by
    simpa only [show (Weighted.responseAffine (0 : Vec d) : Vec d → ℝ) = 0 by
      funext x; exact vecDot_zero_left x,
      show (fun _ : Vec d => (0 : Vec d)) = (0 : Vec d → Vec d) from rfl, sub_zero] using hz
  exact (Weighted.harmonic_replacement_unique hU hne ha
    (liftCellPair_spec hU hne ha 0).1 hs (liftCellPair_spec hU hne ha 0).2 hb).1

/-- The affine seed can be replaced cell by cell without changing the remote obstacle. -/
theorem capacitary_replacement_exists (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) :
    ∃ (f : Vec d → ℝ) (Gf : Vec d → Vec d), MemH1a0 a (originCube 1) f Gf ∧
      (∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → f x = 1) ∧
      (weightedEnergy a (originCube 1) Gf).toReal =
        ((triangulation (d := d) 4).attach.sum fun η =>
          vecDot (capacitaryDirection η)
            (matVecMul (upperResponseOnCell 4 a ha η) (capacitaryDirection η))) /
          ((triangulation (d := d) 4).card : ℝ) := by
  classical
  have hV := originCube_domain (d := d) one_pos
  have hne := originCube_nonempty (d := d) one_pos
  let P (η : SimplexIndex d 4) := liftCellPair
    (simplexCell_isOpenBoundedConvexDomain 4 η) (simplexCell_nonempty 4 η)
    (weightedCoeffOn_simplexCell 4 a ha η) (capacitaryDirection η)
  let cv (η : SimplexIndex d 4) := (P η).1 - Weighted.responseAffine (capacitaryDirection η)
  let cG (η : SimplexIndex d 4) := (P η).2 - fun _ => capacitaryDirection η
  let lv (η : SimplexIndex d 4) := (simplexCell 4 η).indicator (cv η)
  let lG (η : SimplexIndex d 4) := (simplexCell 4 η).indicator (cG η)
  have hP (η : SimplexIndex d 4) : IsWeightedSolution a (simplexCell 4 η) (P η).1 (P η).2 ∧
      MemH1a0 a (simplexCell 4 η) (cv η) (cG η) :=
    liftCellPair_spec _ _ _ _
  have hl (η : SimplexIndex d 4) : MemH1a0 a (originCube 1) (lv η) (lG η) :=
    lift_zero_extension (simplexCell_isOpenBoundedConvexDomain 4 η)
      (simplexCell_nonempty 4 η) hV.isOpen (simplexCell_subset_originCube 4 η) ha (hP η).2
  let v : Vec d → ℝ := ∑ η : SimplexIndex d 4, lv η
  let H : Vec d → Vec d := ∑ η : SimplexIndex d 4, lG η
  have hvH : MemH1a0 a (originCube 1) v H := lift_boundary_finset_sum hV hne ha lv lG hl _
  have hsum {E : Type} [AddCommMonoid E] (L : SimplexIndex d 4 → Vec d → E)
      (η : SimplexIndex d 4) {x : Vec d} (hx : x ∈ simplexCell 4 η) :
      (∑ τ : SimplexIndex d 4, (simplexCell 4 τ).indicator (L τ)) x = L η x := by
    rw [Finset.sum_apply, Finset.sum_eq_single η]
    · exact indicator_of_mem hx _
    · intro τ _ hτη
      exact indicator_of_notMem (fun hτ =>
        disjoint_left.mp (Assembly.ClassicalMomentsImpl.simplexCell_pairwise_disjoint 4 hτη.symm) hx hτ) _
    · simp
  let f := capacitarySeed d + v
  let Gf := smoothGrad (capacitarySeed d) + H
  have hf : MemH1a0 a (originCube 1) f Gf :=
    Weighted.MemH1a0.add hV hne ha (capacitarySeed_memH1a0 a ha) hvH
  have hGcell (η : SimplexIndex d 4) {x : Vec d} (hx : x ∈ simplexCell 4 η) :
      Gf x = (P η).2 x := by
    change smoothGrad (capacitarySeed d) x + H x = _
    have hH : H x = cG η x := by simpa only [H, lG] using hsum cG η hx
    rw [capacitarySeed_gradient η hx, hH]
    dsimp only [cG, Pi.sub_apply]
    abel
  have hfcell (η : SimplexIndex d 4) {x : Vec d} (hx : x ∈ simplexCell 4 η) :
      f x = (P η).1 x + capacitaryConstant η := by
    change capacitarySeed d x + v x = _
    have hv : v x = cv η x := by simpa only [v, lv] using hsum cv η hx
    rw [capacitarySeed_affine η hx, hv]
    dsimp only [cv, Pi.sub_apply]
    change (vecDot (capacitaryDirection η) x + _) +
      ((P η).1 x - vecDot (capacitaryDirection η) x) = _
    ring
  have hfQ : ∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → f x = 1 := by
    have hzero (η : SimplexIndex d 4) : ∀ᵐ x ∂volume.restrict (simplexCell 4 η),
        x ∈ remoteCube d (1 / 2) → (P η).1 x = 0 := by
      by_cases hmeet : (simplexCell 4 η ∩ remoteCube d (1 / 2)).Nonempty
      · have he := (capacitary_cell_meets_obstacle η hmeet).1
        have hz := capacitary_liftCellPair_zero (simplexCell_isOpenBoundedConvexDomain 4 η)
          (simplexCell_nonempty 4 η) (weightedCoeffOn_simplexCell 4 a ha η)
        change ∀ᵐ x ∂volume.restrict (simplexCell 4 η), x ∈ remoteCube d (1 / 2) →
          (liftCellPair _ _ _ (capacitaryDirection η)).1 x = 0
        rw [he]
        filter_upwards [hz] with x hx _
        exact hx
      · filter_upwards [ae_restrict_mem (simplexCell_isOpenBoundedConvexDomain 4 η).isOpen.measurableSet]
          with x hx hQ
        exact (hmeet ⟨x, hx, hQ⟩).elim
    have hall : ∀ᵐ x ∂volume, ∀ η : SimplexIndex d 4, x ∈ simplexCell 4 η →
        x ∈ remoteCube d (1 / 2) → (P η).1 x = 0 := by
      apply ae_all_iff.mpr
      intro η
      exact (ae_restrict_iff' (simplexCell_isOpenBoundedConvexDomain 4 η).isOpen.measurableSet).mp (hzero η)
    have hcover := Assembly.ClassicalMomentsImpl.simplexCell_union_ae (d := d) 4
    rw [ae_restrict_iff' hV.isOpen.measurableSet]
    filter_upwards [hall, hcover] with x hx hc hxV hxQ
    obtain ⟨η, hxη⟩ := mem_iUnion.mp (hc.mpr hxV)
    rw [hfcell η hxη, hx η hxη hxQ,
      (capacitary_cell_meets_obstacle η ⟨x, hxη, hxQ⟩).2, zero_add]
  have hfi := Weighted.MemH1a0.memH1a ha hf
  have hEint := Weighted.quadratic_integrable ha hfi.2.1
    (Weighted.MemH1a.energy_lt_top hV.isOpen ha hfi)
  have hav (η : SimplexIndex d 4) : volumeAverage (simplexCell 4 η)
      (fun x => vecDot (Gf x) (matVecMul (a x) (Gf x))) =
      vecDot (capacitaryDirection η)
        (matVecMul (upperResponseOnCell 4 a ha η) (capacitaryDirection η)) := by
    have hb : MemH1a0 a (simplexCell 4 η)
        (fun x => (P η).1 x - (vecDot (capacitaryDirection η) x + 0))
        (fun x => (P η).2 x - capacitaryDirection η) := by
      have hh := (hP η).2
      change MemH1a0 a (simplexCell 4 η)
        (fun x => (P η).1 x - vecDot (capacitaryDirection η) x)
        (fun x => (P η).2 x - capacitaryDirection η) at hh
      simpa only [add_zero] using hh
    have he := (upperResponse_spec (simplexCell_isOpenBoundedConvexDomain 4 η)
      (simplexCell_nonempty 4 η) (weightedCoeffOn_simplexCell 4 a ha η)).2.2.2.2.1
      (capacitaryDirection η) 0 (P η).1 (P η).2 (hP η).1 hb
    change vecDot (capacitaryDirection η)
      (matVecMul (upperResponseOnCell 4 a ha η) (capacitaryDirection η)) = _ at he
    rw [he]
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (simplexCell_isOpenBoundedConvexDomain 4 η).isOpen.measurableSet]
      with x hx
    rw [hGcell η hx]
  refine ⟨f, Gf, hf, hfQ, ?_⟩
  rw [Weighted.energy_toReal ha hfi.2.1]
  have hp := Assembly.ClassicalMomentsImpl.partition_average 4 hEint
  rw [← hp]
  congr 1
  apply Finset.sum_congr rfl
  intro η _
  exact hav η

end CoarseDeGiorgi.Endpoint
