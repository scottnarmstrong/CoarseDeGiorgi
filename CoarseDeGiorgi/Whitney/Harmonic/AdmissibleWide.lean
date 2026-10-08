module

public import CoarseDeGiorgi.Whitney.Harmonic.GeometryWide
public import CoarseDeGiorgi.Whitney.Harmonic.Admissible
public import CoarseDeGiorgi.Whitney.Harmonic.CellId
public import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
public import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
public import CoarseDeGiorgi.Weighted.TestingCompactSupport
public import CoarseDeGiorgi.Weighted.Lipschitz
public import CoarseDeGiorgi.Weighted.Truncation.Energy

/-! Admissibility of the piecewise harmonic extension: `H = Φ + ξ` with `ξ ∈ H¹_{a,0}`. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

variable {d : ℕ}

open CoarseDeGiorgi.Harnack.Replacement

/-- The piecewise harmonic extension differs from any globally Lipschitz extension `Φ` of `L_h f`
(vanishing off a compact subset of the unit cube) by an element `ξ` of `H¹_{a,0}`. -/
theorem admissible_correction (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) (f : Vec d → ℝ)
    {Φ : Vec d → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ)
    (hΦL : ∀ x ∈ (closedReferenceCube (d := d) τ)ᶜ, Φ x = whitneyAffineExtension τ h f hτ0 hτ1 x)
    (hLzero : ∀ cell : ExteriorCell d τ, cell ∉ whitneySimplicesNear τ h →
      ∀ x ∈ exteriorCellSet cell, whitneyAffineExtension τ h f hτ0 hτ1 x = 0)
    {Kc : Set (Vec d)} (hKc : IsCompact Kc) (hKcO : Kc ⊆ originCube 1)
    (hΦKc : ∀ x, x ∉ Kc → Φ x = 0)
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH) :
    ∃ (ξ : Vec d → ℝ) (Gξ : Vec d → Vec d),
      MemH1a0 a (originCube 1) ξ Gξ ∧
      MemH1a0 a (originCube 1) (Φ + ξ) (smoothGrad Φ + Gξ) ∧
      (∀ᵐ x ∂volume.restrict (originCube (d := d) 1 \ closedReferenceCube (d := d) τ),
        H x = Φ x + ξ x ∧ GH x = smoothGrad Φ x + Gξ x) ∧
      (∀ᵐ x ∂volume.restrict (closedReferenceCube (d := d) τ), ξ x = 0 ∧ Gξ x = 0) := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hτpos : 0 < τ := by linarith
  have hOd : IsOpenBoundedConvexDomain (originCube (d := d) 1) :=
    Whitney.source_cube_domain (by norm_num)
  have hOne : (originCube (d := d) 1).Nonempty := Whitney.source_cube_nonempty (by norm_num)
  set L := whitneyAffineExtension τ h f hτ0 hτ1 with hLdef
  let Near := {c : ExteriorCell d τ // c ∈ whitneySimplicesNear τ h}
  have hspec := fun cell : ExteriorCell d τ =>
    ((whitneyInterpolation_spec hτ0 hτ1 (whitneyFreeValue τ h f)).1).2.2.1 cell
  choose e c hec using hspec
  have hecL (cell : ExteriorCell d τ) : ∀ x ∈ exteriorCellSet cell, L x = vecDot (e cell) x + c cell :=
    hec cell
  have hcellOpen (cell : ExteriorCell d τ) : IsOpenBoundedConvexDomain (exteriorCellSet cell) := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_domain (whitneyCell cell)
  have hcellNe (cell : ExteriorCell d τ) : (exteriorCellSet cell).Nonempty := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_nonempty (whitneyCell cell)
  have hΦcell (cell : ExteriorCell d τ) : ∀ x ∈ exteriorCellSet cell, Φ x = vecDot (e cell) x + c cell :=
    fun x hx => by
      rw [hΦL x (fun hxB => (Set.disjoint_left.mp (cell_disjoint_closedRef hτ0 hτ1 cell)) hx hxB),
        hecL cell x hx]
  have hΓcell (cell : ExteriorCell d τ) :
      ∀ x ∈ exteriorCellSet cell, smoothGrad Φ x = e cell :=
    smoothGrad_eq_of_affine (hcellOpen cell).isOpen (e cell) (c cell) (hΦcell cell)
  have hUV (n : Near) : exteriorCellSet n.1 ⊆ originCube 1 :=
    near_cell_subset_unit hτ0 hτ1 hρ₂ hτρ hh hwidth (by omega) n.1 n.2
  have hdisj : Pairwise (fun n m : Near => Disjoint (exteriorCellSet n.1) (exteriorCellSet m.1)) :=
    fun n m hnm => exteriorCells_disjoint hτ0 hτ1 n.1 m.1 (fun he => hnm (Subtype.ext he))
  have hMemΦ : MemH1a a (originCube 1) Φ (smoothGrad Φ) :=
    Weighted.memH1a_of_lipschitzOn hOd hOne ha hΦ.lipschitzOnWith EventuallyEq.rfl
  have hfinite := Weighted.MemH1a.energy_lt_top hOd.isOpen ha hMemΦ
  have hΦ0 : MemH1a0 a (originCube 1) Φ (smoothGrad Φ) :=
    Weighted.MemH1a.memH1a0_of_compact_support hOd hOne ha hMemΦ hKc hKcO
      (Filter.Eventually.of_forall fun x hx => hΦKc x hx)
  obtain ⟨ξ, Gξ, hξ, hξcell, hξzero⟩ := Whitney.source_correction_exists hOd hOne ha
    (fun n : Near => exteriorCellSet n.1) (fun n => hcellOpen n.1) (fun n => hcellNe n.1) hUV hdisj
    (fun n => e n.1) (smoothGrad Φ) (fun n x hx => hΓcell n.1 x hx) hfinite
  have hψ : MemH1a0 a (originCube 1) (Φ + ξ) (smoothGrad Φ + Gξ) :=
    Weighted.MemH1a0.add hOd hOne ha hΦ0 hξ
  have hvalues (n : Near) : (Φ + ξ) =ᵐ[volume.restrict (exteriorCellSet n.1)]
      (fun x => (Whitney.liftCellPair (hcellOpen n.1) (hcellNe n.1)
        (Whitney.lift_coeff_mono ha (hUV n)) (e n.1)).1 x + c n.1) := by
    filter_upwards [hξcell n, ae_restrict_mem (hcellOpen n.1).isOpen.measurableSet] with x hx hxU
    change Φ x + ξ x = _
    rw [hx, hΦcell n.1 x hxU]
    change (vecDot (e n.1) x + c n.1) + ((Whitney.liftCellPair (hcellOpen n.1) (hcellNe n.1)
        (Whitney.lift_coeff_mono ha (hUV n)) (e n.1)).1 x - vecDot (e n.1) x) = _
    ring
  have hJcell (n : Near) : (smoothGrad Φ + Gξ) =ᵐ[volume.restrict (exteriorCellSet n.1)]
      (Whitney.liftCellPair (hcellOpen n.1) (hcellNe n.1)
        (Whitney.lift_coeff_mono ha (hUV n)) (e n.1)).2 :=
    Adapters.lift_testing_harmonic_cell_gradient hOd hOne ha (hcellOpen n.1) (hcellNe n.1)
      (hUV n) (e n.1) (c n.1) hψ (hvalues n)
  have hlevel := Weighted.MemH1a.gradient_zero_on_level hOd hOne ha
    (Weighted.MemH1a0.memH1a ha hξ) 0
  have hΓL (cell : ExteriorCell d τ) : ∀ x ∈ exteriorCellSet cell, smoothGrad L x = e cell :=
    smoothGrad_eq_of_affine (hcellOpen cell).isOpen (e cell) (c cell) (hecL cell)
  have hBO : closedReferenceCube (d := d) τ ⊆ originCube 1 := by
    intro x hx i
    have := hx i
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  -- ξ and its gradient vanish off the near cells
  have hxi0 : ∀ᵐ x ∂volume.restrict (originCube (d := d) 1 \ ⋃ n : Near, exteriorCellSet n.1),
      ξ x = 0 ∧ Gξ x = 0 := by
    have hl := ae_mono (Measure.restrict_mono (sdiff_subset :
      originCube (d := d) 1 \ ⋃ n : Near, exteriorCellSet n.1 ⊆ originCube 1) le_rfl) hlevel
    filter_upwards [hξzero, hl] with x h1 h2
    refine ⟨by simpa using h1, ?_⟩
    have h3 : Set.indicator {x | ξ x = 0} Gξ x = 0 := h2
    rw [Set.indicator_of_mem (show x ∈ {x | ξ x = 0} from by simpa using h1)] at h3
    exact h3
  refine ⟨ξ, Gξ, hξ, hψ, ?_, ?_⟩
  have hSm : MeasurableSet (originCube (d := d) 1 \ closedReferenceCube τ) :=
    hOd.isOpen.measurableSet.diff (isClosed_closedRef hτpos.le).measurableSet
  have hcm (cell : ExteriorCell d τ) : MeasurableSet (exteriorCellSet cell) :=
    (hcellOpen cell).isOpen.measurableSet
  · have hcellwise (cell : ExteriorCell d τ) :
        ∀ᵐ x ∂volume.restrict (exteriorCellSet cell ∩ (originCube (d := d) 1 \ closedReferenceCube τ)),
          H x = Φ x + ξ x ∧ GH x = smoothGrad Φ x + Gξ x := by
      by_cases hnear : cell ∈ whitneySimplicesNear τ h
      · let n : Near := ⟨cell, hnear⟩
        obtain ⟨hsol, h0⟩ := (hHGH cell).1 hnear
        have h0' : MemH1a0 a (exteriorCellSet cell) (fun x => H x - L x) (fun x => GH x - e cell) := by
          refine memH1a0_congr_ae h0 EventuallyEq.rfl ?_
          filter_upwards [ae_restrict_mem (hcellOpen cell).isOpen.measurableSet] with x hx
          rw [hΓL cell x hx]
        have hid := cell_identification (hcellOpen cell) (hcellNe cell)
          (Whitney.lift_coeff_mono ha (hUV n)) (e cell) (c cell) (L := L) (fun x hx => hecL cell x hx)
          hsol h0'
        apply ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_left)
        filter_upwards [hid.1, hid.2, hvalues n, hJcell n] with x h1 h2 h3 h4
        refine ⟨?_, ?_⟩
        · rw [h1]
          have : Φ x + ξ x = (Φ + ξ) x := rfl
          rw [this, h3]
        · rw [h2]
          have : smoothGrad Φ x + Gξ x = (smoothGrad Φ + Gξ) x := rfl
          rw [this, h4]
      · have hz := (hHGH cell).2 hnear
        have hnotU : exteriorCellSet cell ∩ originCube 1 ⊆
            originCube (d := d) 1 \ ⋃ n : Near, exteriorCellSet n.1 := by
          intro x ⟨hx, hxO⟩
          refine ⟨hxO, ?_⟩
          intro hU
          obtain ⟨n, hn⟩ := mem_iUnion.mp hU
          have hne : n.1 ≠ cell := fun he => hnear (he ▸ n.2)
          exact (Set.disjoint_left.mp (exteriorCells_disjoint hτ0 hτ1 n.1 cell hne)) hn hx
        have hxi : ∀ᵐ x ∂volume.restrict (exteriorCellSet cell ∩ originCube (d := d) 1),
            ξ x = 0 ∧ Gξ x = 0 :=
          ae_restrict_of_ae_restrict_of_subset hnotU hxi0
        have hxi' : ∀ᵐ x ∂volume.restrict (exteriorCellSet cell ∩
            (originCube (d := d) 1 \ closedReferenceCube τ)), ξ x = 0 ∧ Gξ x = 0 :=
          ae_restrict_of_ae_restrict_of_subset
            (Set.inter_subset_inter_right _ sdiff_subset) hxi
        have hz' : ∀ᵐ x ∂volume.restrict (exteriorCellSet cell ∩
            (originCube (d := d) 1 \ closedReferenceCube τ)), H x = 0 ∧ GH x = 0 :=
          ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hz
        have hΦ0 (x : Vec d) (hx : x ∈ exteriorCellSet cell) : Φ x = 0 := by
          rw [hΦL x (fun hxB => (Set.disjoint_left.mp (cell_disjoint_closedRef hτ0 hτ1 cell)) hx hxB)]
          exact hLzero cell hnear x hx
        have hΓ0 : ∀ x ∈ exteriorCellSet cell, smoothGrad Φ x = 0 := by
          have := smoothGrad_eq_of_affine (hcellOpen cell).isOpen (0 : Vec d) 0
            (Φ := Φ) (fun y hy => by rw [hΦ0 y hy]; simp [vecDot_zero_left])
          exact this
        have hmem : ∀ᵐ x ∂volume.restrict (exteriorCellSet cell ∩
            (originCube (d := d) 1 \ closedReferenceCube τ)), x ∈ exteriorCellSet cell := by
          filter_upwards [ae_restrict_mem ((hcm cell).inter hSm)] with x hx using hx.1
        filter_upwards [hxi', hz', hmem] with x h1 h2 hx
        refine ⟨?_, ?_⟩
        · rw [h2.1, hΦ0 x hx, h1.1]; ring
        · rw [h2.2, hΓ0 x hx, h1.2]; simp
    have hcover := ae_exists_cell (d := d) hτ0 hτ1
    have hU := (ae_restrict_iUnion_iff (μ := volume.restrict (originCube (d := d) 1 \ closedReferenceCube τ))
      (fun cell : ExteriorCell d τ => exteriorCellSet cell)
      (fun x => H x = Φ x + ξ x ∧ GH x = smoothGrad Φ x + Gξ x)).mpr (fun cell => by
        rw [Measure.restrict_restrict (hcm cell)]
        exact hcellwise cell)
    rw [ae_restrict_iff' (MeasurableSet.iUnion hcm)] at hU
    filter_upwards [ae_restrict_of_ae hcover, ae_restrict_mem hSm, hU] with x h1 h2 h3
    obtain ⟨cell, hcell⟩ := h1 (fun hB => h2.2 hB)
    exact h3 (mem_iUnion.mpr ⟨cell, hcell⟩)
  · have hBsub : closedReferenceCube (d := d) τ ⊆
        originCube (d := d) 1 \ ⋃ n : Near, exteriorCellSet n.1 := by
      intro x hx
      refine ⟨closedRef_subset_unit hτ1 hx, ?_⟩
      intro hU
      obtain ⟨n, hn⟩ := mem_iUnion.mp hU
      exact (Set.disjoint_left.mp (cell_disjoint_closedRef hτ0 hτ1 n.1)) hn hx
    exact ae_restrict_of_ae_restrict_of_subset hBsub hxi0

end CoarseDeGiorgi.Whitney.Harmonic.Wide
