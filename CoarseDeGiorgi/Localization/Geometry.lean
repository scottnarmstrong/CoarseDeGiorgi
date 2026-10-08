module

public import CoarseDeGiorgi.Statements.AuxCube
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # The fixed lattice cover used for compact localization

The auxiliary cubes are the cubes `auxCube`, of side `3 * 3^(-m)`.
The central thirds are closed, so lattice boundaries are covered.
-/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization Set
open scoped BigOperators
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

/-- Grid spacing, one third of the auxiliary cube side. -/
def gridSpacing (m : ℤ) : ℝ := (3 : ℝ) ^ (-m)

/-- The center of an auxiliary cube `auxCube`. -/
def gridCenter (m : ℤ) (z : Fin d → ℤ) : Vec d :=
  fun i => (z i : ℝ) * gridSpacing m

/-- Closed central third used to select the cover. -/
def centralCube (m : ℤ) (z : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - gridCenter m z i| ≤ gridSpacing m / 2}

/-- Closed larger cube, including the boundary for the overlap estimate. -/
def closedAuxCube (m : ℤ) (z : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - gridCenter m z i| ≤ 3 * gridSpacing m / 2}

/-- Open centered cube at a general radius. -/
def radiusCube (R : ℝ) : Set (Vec d) := {x | ∀ i, |x i| < R / 2}

/-- The closed annulus used in the surface version of localization. -/
def localizationAnnulus (ρ R : ℝ) : Set (Vec d) :=
  {x | ρ + (R - ρ) / 8 ≤ 2 * ‖x‖ ∧ 2 * ‖x‖ ≤ ρ + 5 * (R - ρ) / 8}

theorem gridSpacing_pos (m : ℤ) : 0 < gridSpacing m := by
  unfold gridSpacing
  positivity

theorem auxCube_eq_coordinates (m : ℤ) (z : Fin d → ℤ) :
    auxCube m z = {x | ∀ i, |x i - gridCenter m z i| < 3 * gridSpacing m / 2} := by
  unfold auxCube gridCenter gridSpacing
  rw [show 1 - m = -m + 1 by omega, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [mul_comm]

theorem isOpen_auxCube (m : ℤ) (z : Fin d → ℤ) : IsOpen (auxCube m z) := by
  rw [auxCube_eq_coordinates]
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i : Continuous (fun x : Vec d => x i)).sub continuous_const).abs continuous_const

theorem centralCube_subset_auxCube (m : ℤ) (z : Fin d → ℤ) :
    centralCube m z ⊆ auxCube m z := by
  rw [auxCube_eq_coordinates]
  intro x hx i
  exact (hx i).trans_lt (by linarith only [gridSpacing_pos m])

theorem auxCube_subset_closedAuxCube (m : ℤ) (z : Fin d → ℤ) :
    auxCube m z ⊆ closedAuxCube m z := by
  rw [auxCube_eq_coordinates]
  intro x hx i
  exact (hx i).le

/-- Round each coordinate to the nearest grid center. -/
def nearestGrid (m : ℤ) (x : Vec d) : Fin d → ℤ :=
  fun i => ⌊x i / gridSpacing m + 1 / 2⌋

theorem mem_centralCube_nearestGrid (m : ℤ) (x : Vec d) :
    x ∈ centralCube m (nearestGrid m x) := by
  intro i
  have hl := Int.floor_le (x i / gridSpacing m + 1 / 2)
  have hu := Int.lt_floor_add_one (x i / gridSpacing m + 1 / 2)
  have hs := gridSpacing_pos m
  change |x i - (⌊x i / gridSpacing m + 1 / 2⌋ : ℝ) * gridSpacing m| ≤ _
  apply abs_le.mpr
  constructor
  · have h := (mul_le_mul_of_nonneg_right hl hs.le)
    rw [add_mul, div_mul_cancel₀ _ hs.ne'] at h
    linarith only [h]
  · have h := (mul_lt_mul_of_pos_right hu hs)
    rw [add_mul, add_mul, div_mul_cancel₀ _ hs.ne'] at h
    linarith only [h]

/-- Every larger cube selected by a bounded target stays in the indicated radius. -/
theorem closedAuxCube_subset_radiusCube_of_meets {m : ℤ} {z : Fin d → ℤ}
    {K : Set (Vec d)} {a R : ℝ}
    (hK : ∀ y ∈ K, ∀ i, |y i| ≤ a / 2)
    (hmargin : a + 4 * gridSpacing m < R)
    (hmeet : ∃ y ∈ K, y ∈ centralCube m z) :
    closedAuxCube m z ⊆ radiusCube R := by
  obtain ⟨y, hy, hyc⟩ := hmeet
  intro x hx i
  have hdist : |x i - y i| ≤ 2 * gridSpacing m := by
    calc
      _ ≤ |x i - gridCenter m z i| + |gridCenter m z i - y i| := abs_sub_le _ _ _
      _ ≤ 2 * gridSpacing m := by rw [abs_sub_comm (gridCenter m z i)]; linarith only [hx i, hyc i]
  have hab := abs_add_le (x i - y i) (y i)
  rw [sub_add_cancel] at hab
  change |x i| < R / 2
  linarith only [hab, hdist, hK y hy i, hmargin]

/-- Four consecutive integer choices suffice in each coordinate for closed-cube overlap. -/
def overlapChoices (m : ℤ) (x : Vec d) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌊x i / gridSpacing m - 3 / 2⌋
    (⌊x i / gridSpacing m - 3 / 2⌋ + 3)

/-- Membership in a closed auxiliary cube restricts its center to four choices per coordinate. -/
theorem mem_overlapChoices_of_mem_closedAuxCube {m : ℤ} {x : Vec d} {z : Fin d → ℤ}
    (hx : x ∈ closedAuxCube m z) : z ∈ overlapChoices m x := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hs := gridSpacing_pos m
  have hi := abs_le.mp (hx i)
  have hlo : x i / gridSpacing m - 3 / 2 ≤ (z i : ℝ) := by
    have h : x i ≤ ((z i : ℝ) + 3 / 2) * gridSpacing m := by
      dsimp only [gridCenter] at hi
      linarith only [hi.2]
    have hh := (div_le_iff₀ hs).mpr h
    linarith only [hh]
  have hhi : (z i : ℝ) ≤ x i / gridSpacing m + 3 / 2 := by
    have h : ((z i : ℝ) - 3 / 2) * gridSpacing m ≤ x i := by
      dsimp only [gridCenter] at hi
      linarith only [hi.1]
    have hh := (le_div_iff₀ hs).mpr h
    linarith only [hh]
  have hf := Int.floor_le (x i / gridSpacing m - 3 / 2)
  have hg := Int.lt_floor_add_one (x i / gridSpacing m - 3 / 2)
  have hfz : ⌊x i / gridSpacing m - 3 / 2⌋ ≤ z i :=
    Int.cast_le.mp (hf.trans hlo)
  have hzu : z i < ⌊x i / gridSpacing m - 3 / 2⌋ + 4 := by
    exact_mod_cast (by push_cast; linarith only [hg, hhi] :
      (z i : ℝ) < ((⌊x i / gridSpacing m - 3 / 2⌋ + 4 : ℤ) : ℝ))
  -- A grid boundary can attain the lower endpoint, so use floor rather than floor+1.
  constructor <;> omega

/-- The closed-cube overlap is bounded independently of the number of selected cubes. -/
theorem card_filter_closedAuxCube_le (m : ℤ) (Z : Finset (Fin d → ℤ)) (x : Vec d) :
    (Z.filter fun z => x ∈ closedAuxCube m z).card ≤ 4 ^ d := by
  classical
  have hc : (overlapChoices m x).card = 4 ^ d := by
    unfold overlapChoices
    rw [Fintype.card_piFinset]
    have hcard (i : Fin d) :
        (Finset.Icc ⌊x i / gridSpacing m - 3 / 2⌋ (⌊x i / gridSpacing m - 3 / 2⌋ + 3)).card = 4 := by
      rw [Int.card_Icc]
      omega
    simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hc]
  apply Finset.card_le_card
  intro z hz
  exact mem_overlapChoices_of_mem_closedAuxCube (Finset.mem_filter.mp hz).2

/-- A finite box containing the centers of all relevant cubes. -/
def centerBox (m : ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-⌈1 / gridSpacing m⌉) ⌈1 / gridSpacing m⌉

/-- Exactly the central thirds meeting the target are selected. -/
def coverIndices (m : ℤ) (K : Set (Vec d)) : Finset (Fin d → ℤ) :=
  (centerBox m).filter fun z => ∃ y ∈ K, y ∈ centralCube m z

theorem mem_centerBox_of_meets {m : ℤ} (hs1 : gridSpacing m ≤ 1)
    {K : Set (Vec d)} (hK : ∀ y ∈ K, ∀ i, |y i| ≤ 1 / 2)
    {z : Fin d → ℤ} (hmeet : ∃ y ∈ K, y ∈ centralCube m z) : z ∈ centerBox m := by
  classical
  obtain ⟨y, hy, hc⟩ := hmeet
  apply Fintype.mem_piFinset.mpr
  intro i
  have hs := gridSpacing_pos m
  have hh := abs_sub_le (gridCenter m z i) (y i) 0
  simp only [sub_zero, abs_sub_comm (gridCenter m z i)] at hh
  have hbound : |gridCenter m z i| ≤ 1 := by linarith only [hh, hc i, hK y hy i, hs1]
  have hz : |(z i : ℝ)| ≤ 1 / gridSpacing m := by
    apply (le_div_iff₀ hs).mpr
    simpa only [gridCenter, abs_mul, abs_of_pos hs] using hbound
  have he := hz.trans (Int.le_ceil (1 / gridSpacing m))
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (abs_le.mp he).1
  · exact_mod_cast (abs_le.mp he).2

theorem coverIndices_covers {m : ℤ} (hs1 : gridSpacing m ≤ 1)
    {K : Set (Vec d)} (hK : ∀ y ∈ K, ∀ i, |y i| ≤ 1 / 2) {x : Vec d} (hx : x ∈ K) :
    ∃ z ∈ coverIndices m K, x ∈ centralCube m z := by
  classical
  have hnear := mem_centralCube_nearestGrid m x
  refine ⟨nearestGrid m x, Finset.mem_filter.mpr ⟨?_, ⟨x, hx, hnear⟩⟩, hnear⟩
  exact mem_centerBox_of_meets hs1 hK ⟨x, hx, hnear⟩

theorem coverIndices_meets {m : ℤ} {K : Set (Vec d)} {z : Fin d → ℤ}
    (hz : z ∈ coverIndices m K) : ∃ y ∈ K, y ∈ centralCube m z := by
  classical
  exact (Finset.mem_filter.mp hz).2

/-- Selected auxiliary cubes are contained in the larger open cube, with a strict margin. -/
theorem selected_closedAuxCube_subset {m : ℤ} {K : Set (Vec d)} {a R : ℝ}
    (hK : ∀ y ∈ K, ∀ i, |y i| ≤ a / 2) (hm : a + 4 * gridSpacing m < R)
    {z : Fin d → ℤ} (hz : z ∈ coverIndices m K) :
    closedAuxCube m z ⊆ radiusCube R :=
  closedAuxCube_subset_radiusCube_of_meets hK hm (coverIndices_meets hz)

/-- Counting the bounded lattice box gives a polynomial bound in inverse spacing. -/
theorem card_coverIndices_le {m : ℤ} (hs1 : gridSpacing m ≤ 1) (K : Set (Vec d)) :
    ((coverIndices m K).card : ℝ) ≤ (5 / gridSpacing m) ^ d := by
  classical
  let L : ℤ := ⌈1 / gridSpacing m⌉
  have hs := gridSpacing_pos m
  have hL : 0 ≤ L := Int.ceil_nonneg (by positivity)
  have hc : (centerBox (d := d) m).card = (2 * L + 1).toNat ^ d := by
    simp only [centerBox, Fintype.card_piFinset, Int.card_Icc]
    have he : ⌈1 / gridSpacing m⌉ + 1 - -⌈1 / gridSpacing m⌉ = 2 * L + 1 := by dsimp [L]; ring
    simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbox : ((coverIndices m K).card : ℝ) ≤ ((centerBox (d := d) m).card : ℝ) := by
    exact_mod_cast Finset.card_filter_le (centerBox m) _
  rw [hc, Nat.cast_pow] at hbox
  have hbase : (((2 * L + 1).toNat : ℕ) : ℝ) ≤ 5 / gridSpacing m := by
    have hn : (((2 * L + 1).toNat : ℕ) : ℝ) = ((2 * L + 1 : ℤ) : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ 2 * L + 1 by omega))
    rw [hn]
    have hceil := Int.ceil_lt_add_one (1 / gridSpacing m)
    have hone : 1 ≤ 1 / gridSpacing m := (one_le_div hs).mpr hs1
    dsimp only [L]
    push_cast
    rw [show 5 / gridSpacing m = 5 * (1 / gridSpacing m) by ring]
    linarith only [hceil, hone]
  exact hbox.trans (pow_le_pow_left₀ (by positivity) hbase d)


/-- Margin for the annular cover at the source's chosen scale. -/
theorem annular_margin {ρ R : ℝ} {m : ℤ} (hρR : ρ < R)
    (hs : gridSpacing m ≤ (R - ρ) / 64) :
    ρ + 5 * (R - ρ) / 8 + 4 * gridSpacing m < R := by
  linarith only [hρR, hs]

/-- Margin for the inner-cube version at the same scale. -/
theorem inner_margin {ρ R : ℝ} {m : ℤ} (hρR : ρ < R)
    (hs : gridSpacing m ≤ (R - ρ) / 64) : ρ + 4 * gridSpacing m < R := by
  linarith only [hρR, hs]

/-- Quantitative number of cubes, with constant independent of the target set and radii. -/
theorem card_coverIndices_le_gap {m : ℤ} {δ : ℝ} (hδ : 0 < δ) (hs1 : gridSpacing m ≤ 1)
    (hs : δ / 192 < gridSpacing m) (K : Set (Vec d)) :
    ((coverIndices m K).card : ℝ) ≤ (960 : ℝ) ^ d * δ ^ (-(d : ℝ)) := by
  have hratio : 5 / gridSpacing m ≤ 960 / δ := by
    apply (div_le_div_iff₀ (gridSpacing_pos m) hδ).mpr
    linarith only [hs]
  calc
    _ ≤ (5 / gridSpacing m) ^ d := card_coverIndices_le hs1 K
    _ ≤ (960 / δ) ^ d := pow_le_pow_left₀ (div_nonneg (by norm_num) (gridSpacing_pos m).le) hratio d
    _ = _ := by
      rw [div_pow, Real.rpow_neg hδ.le, Real.rpow_natCast]
      exact div_eq_mul_inv _ _

/-- The larger closed cube is a compact sup-norm ball. -/
theorem closedAuxCube_eq_closedBall (m : ℤ) (z : Fin d → ℤ) :
    closedAuxCube m z = Metric.closedBall (gridCenter m z) (3 * gridSpacing m / 2) := by
  ext x
  rw [mem_closedBall_iff_norm,
    pi_norm_le_iff_of_nonneg (by linarith only [gridSpacing_pos m] : 0 ≤ 3 * gridSpacing m / 2)]
  rfl

theorem isCompact_closedAuxCube (m : ℤ) (z : Fin d → ℤ) :
    IsCompact (closedAuxCube m z) := by
  rw [closedAuxCube_eq_closedBall]
  exact isCompact_closedBall _ _

theorem closure_auxCube_subset (m : ℤ) (z : Fin d → ℤ) :
    closure (auxCube m z) ⊆ closedAuxCube m z :=
  closure_minimal (auxCube_subset_closedAuxCube m z) (isCompact_closedAuxCube m z).isClosed

/-- Compact containment includes the full auxiliary-cube closure. -/
theorem selected_auxCube_compactly_contained {m : ℤ} {K : Set (Vec d)} {a R : ℝ}
    (hK : ∀ y ∈ K, ∀ i, |y i| ≤ a / 2) (hm : a + 4 * gridSpacing m < R)
    {z : Fin d → ℤ} (hz : z ∈ coverIndices m K) :
    IsCompact (closure (auxCube m z)) ∧ closure (auxCube m z) ⊆ radiusCube R := by
  refine ⟨(isCompact_closedAuxCube m z).of_isClosed_subset isClosed_closure (closure_auxCube_subset m z), ?_⟩
  exact (closure_auxCube_subset m z).trans (selected_closedAuxCube_subset hK hm hz)

/-- The source factor-three scale interval is inhabited. -/
theorem exists_localization_scale {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ m : ℤ, 0 ≤ m ∧ δ / 192 < gridSpacing m ∧ gridSpacing m ≤ δ / 64 := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < δ / 64 by positivity) (show δ / 64 ≤ 1 by linarith only [hδ1])
    (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  have he (k : ℕ) : gridSpacing (k : ℤ) = (1 / 3 : ℝ) ^ k := by
    simp only [gridSpacing, zpow_neg, zpow_natCast, one_div, inv_pow]
  by_cases heq : δ / 64 = (1 / 3 : ℝ) ^ n
  · refine ⟨n, by positivity, ?_, ?_⟩
    · rw [he, ← heq]
      linarith only [hδ]
    · rw [he, ← heq]
  · have hstrict : δ / 64 < (1 / 3 : ℝ) ^ n := lt_of_le_of_ne hnhi heq
    have hp := mul_lt_mul_of_pos_right hstrict (by norm_num : (0 : ℝ) < 1 / 3)
    refine ⟨(n + 1 : ℕ), by positivity, ?_, ?_⟩
    · rw [he, pow_succ]
      linarith only [hp]
    · rw [he]
      exact hnlo.le

end
end CoarseDeGiorgi.Localization
