import CoarseDeGiorgi.Whitney.Interpolation.GlueCells
import CoarseDeGiorgi.Statements.WhitneyCubesProperties
import CoarseDeGiorgi.Statements.IsFreeVertex
import CoarseDeGiorgi.Whitney.SeedClosedCover

/-! # Geometry of Whitney cubes and cells at the mesh of their children

Neighboring selected cubes differ by at most one scale; nodes of a mesh inside a cube; the
dictionary between `ExteriorCell` and the Kuhn cells `cellN`; closed cells cover closed cubes. -/

namespace CoarseDeGiorgi.Whitney.Interpolation

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ} {τ : ℝ}

/-- Touching selected cubes: `ℓ(D) ≤ 3 ℓ(E)` (`e.whitney.neighbors`). -/
theorem scale_le_succ_of_touch (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D E : TriadicCube d}
    (hD : D ∈ whitneyCubes τ) (hE : E ∈ whitneyCubes τ) {x : Vec d}
    (hxD : x ∈ closedTriadicCube D) (hxE : x ∈ closedTriadicCube E) :
    D.scale ≤ E.scale + 1 := by
  obtain ⟨_, _, _, h4⟩ := whitney_cubes (d := d) hτ0 hτ1
  obtain ⟨a1, a2, _⟩ := h4 D hD x hxD
  obtain ⟨_, _, b3⟩ := h4 E hE x hxE
  have h : 2 * cubeScaleFactor D < 9 * cubeScaleFactor E := by linarith
  by_contra hn
  push Not at hn
  have h1 : (3 : ℝ) ^ (E.scale + 2) ≤ 3 ^ D.scale :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h9 : (3 : ℝ) ^ (E.scale + 2) = 9 * 3 ^ E.scale := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have := pos_zpow3 E.scale
  unfold cubeScaleFactor at h
  linarith

theorem three_zpow_split {n s : ℤ} (h : n ≤ s) :
    ∃ N : ℕ, (3 : ℝ) ^ s = 3 ^ n * (2 * N + 1) := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  have hs : s = n + k := by omega
  obtain ⟨N, hN⟩ : Odd (3 ^ k : ℕ) := Odd.pow (by decide)
  refine ⟨N, ?_⟩
  rw [hs, zpow_add₀ (by norm_num), zpow_natCast]
  congr 1
  have : ((3 ^ k : ℕ) : ℝ) = 2 * N + 1 := by exact_mod_cast hN
  push_cast at this
  exact this

/-- Nodes of a coarser mesh are nodes of a finer mesh. -/
theorem nodeN_nest {n s : ℤ} (h : n ≤ s) (m : Fin d → ℤ) : ∃ m' : Fin d → ℤ, nodeN s m = nodeN n m' := by
  obtain ⟨N, hN⟩ := three_zpow_split h
  refine ⟨fun i => (2 * N + 1) * m i + N, ?_⟩
  funext i
  simp only [nodeN, hN]
  push_cast
  ring

/-- Support of a hat of mesh `3^n` in a closed cube of scale `≥ n` stays in the cube. -/
theorem nodeN_mem_closedCube {n : ℤ} {G : TriadicCube d} (hn : n ≤ G.scale) {m : Fin d → ℤ}
    {x : Vec d} (hx : x ∈ closedTriadicCube G) (h : hatN n m x ≠ 0) :
    nodeN n m ∈ closedTriadicCube G := by
  obtain ⟨N, hN⟩ := three_zpow_split hn
  intro i
  have hxi := hx i
  have hh := abs_sub_lt_of_hatN_ne_zero h i
  have hp := pos_zpow3 n
  simp only [triadicCenter, cubeScaleFactor] at hxi ⊢
  rw [hN] at hxi ⊢
  rw [abs_le] at hxi
  rw [abs_lt] at hh
  rw [abs_le]
  have hnode : nodeN n m i = (3 : ℝ) ^ n * ((m i : ℝ) + 1 / 2) := rfl
  rw [hnode] at hh ⊢
  have hmB : m i ≤ G.index i * (2 * N + 1) + N := by
    by_contra hc
    push Not at hc
    have h1 : ((G.index i * (2 * N + 1) + N : ℤ) : ℝ) + 1 ≤ m i := by exact_mod_cast hc
    push_cast at h1
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h1)]
  have hmA : G.index i * (2 * N + 1) - N - 1 ≤ m i := by
    by_contra hc
    push Not at hc
    have h1 : (m i : ℝ) + 1 ≤ ((G.index i * (2 * N + 1) - N - 1 : ℤ) : ℝ) := by exact_mod_cast hc
    push_cast at h1
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h1)]
  have hB : (m i : ℝ) ≤ G.index i * (2 * N + 1) + N := by exact_mod_cast hmB
  have hA : (G.index i : ℝ) * (2 * N + 1) - N - 1 ≤ m i := by exact_mod_cast hmA
  constructor <;> nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hB), mul_nonneg hp.le (sub_nonneg.mpr hA)]

/-- A selected closed cube misses the reference cube. -/
theorem closedCube_disjoint_ref {D : TriadicCube d} (hD : D ∈ whitneyCubes τ) :
    ∀ x ∈ closedTriadicCube D, x ∉ closedReferenceCube (d := d) τ := by
  intro x hx hxr
  have hadm := hD.1
  have hs : 0 < cubeScaleFactor D := pos_zpow3 _
  have : x ∈ fivefoldClosedTriadicCube D := fun i => by
    have := hx i
    linarith
  exact Set.disjoint_left.mp hadm this hxr

/-- The integer center index of the child cube of an exterior cell. -/
def cellQ (cell : ExteriorCell d τ) : Fin d → ℤ :=
  fun i => 3 * cell.1.val.index i + ((cell.2.1 i).val : ℤ) - 1

theorem simplex_eq_kuhn (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    simplex n π z = Foundations.Simplex.kuhnSimplex n π z := by
  have hp := pos_zpow3 n
  ext x
  simp only [simplex, Foundations.Simplex.kuhnSimplex, Foundations.Simplex.simplexCube,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, rfl, hy, hmono⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · have := hy i
      simp only [Pi.add_apply, add_sub_cancel_left]
      constructor <;> nlinarith [this.1, this.2]
    · have := hmono i j hij
      simp only [Pi.add_apply, add_sub_cancel_left]
      exact mul_lt_mul_of_pos_left this hp
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (x i - z i) / (3 : ℝ) ^ n, ?_, fun i => ?_, fun i j hij => ?_⟩
    · funext i
      simp only [Pi.add_apply]
      field_simp
      ring
    · have := h1 i
      constructor
      · rw [lt_div_iff₀ hp]; linarith [this.1]
      · rw [div_lt_iff₀ hp]; linarith [this.2]
    · have := h2 hij
      exact (div_lt_div_iff_of_pos_right hp).mpr this

theorem exteriorCellCenter_eq (cell : ExteriorCell d τ) :
    exteriorCellCenter cell = fun i => (3 : ℝ) ^ (cell.1.val.scale - 1) * (cellQ cell i : ℝ) := by
  funext i
  simp only [exteriorCellCenter, triadicCenter, cubeScaleFactor, cellQ]
  rw [zpow_sub_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  push_cast
  field_simp
  ring

theorem exteriorCellSet_eq (cell : ExteriorCell d τ) :
    exteriorCellSet cell = cellN (cell.1.val.scale - 1) (cellQ cell) cell.2.2 := by
  unfold exteriorCellSet
  rw [simplex_eq_kuhn, exteriorCellCenter_eq]

theorem exteriorCellVertex_eq (cell : ExteriorCell d τ) (j : Fin (d + 1)) :
    exteriorCellVertex cell j =
      nodeN (cell.1.val.scale - 1) (seedKuhnVertexIndex (cellQ cell) cell.2.2 j) := by
  funext i
  have hc := congrFun (exteriorCellCenter_eq cell) i
  simp only [exteriorCellVertex, nodeN, seedKuhnVertexIndex]
  rw [hc]
  split_ifs <;> push_cast <;> ring

theorem closure_exteriorCellSet_subset (cell : ExteriorCell d τ) :
    closure (exteriorCellSet cell) ⊆ closedTriadicCube cell.1.val := by
  have h : exteriorCellSet cell = seedCellSet ⟨cell.1.val, cell.2.1, cell.2.2⟩ := by
    unfold exteriorCellSet seedCellSet seedCellCenter
    rw [simplex_eq_kuhn]
    rfl
  rw [h]
  exact seedCell_closure_subset_parent _

theorem exists_cell_of_mem_closedCube {D : TriadicCube d} (hD : D ∈ whitneyCubes τ) {x : Vec d}
    (hx : x ∈ closedTriadicCube D) :
    ∃ cell : ExteriorCell d τ, cell.1.val = D ∧ x ∈ closure (exteriorCellSet cell) := by
  obtain ⟨c, hc, hxc⟩ := seedParent_closedCell_cover D hx
  obtain ⟨cube, bins, order⟩ := c
  simp only at hc
  subst hc
  refine ⟨(⟨cube, hD⟩, (bins, order)), rfl, ?_⟩
  have h : exteriorCellSet ((⟨cube, hD⟩, (bins, order)) : ExteriorCell d τ) =
      seedCellSet ⟨cube, bins, order⟩ := by
    unfold exteriorCellSet seedCellSet seedCellCenter
    rw [simplex_eq_kuhn]
    rfl
  rw [h]
  exact hxc

/-- A node of the cell's own mesh lying in the closed cell is one of its vertices. -/
theorem vertex_of_node_mem_closure {cell : ExteriorCell d τ} {m : Fin d → ℤ} {w : Vec d}
    (hw : w = nodeN (cell.1.val.scale - 1) m) (hcl : w ∈ closure (exteriorCellSet cell)) :
    ∃ j, exteriorCellVertex cell j = w := by
  rw [exteriorCellSet_eq] at hcl
  have h1 : hatN (cell.1.val.scale - 1) m w ≠ 0 := by
    rw [hw, hatN_apply_node, ite_eq_left rfl]; exact one_ne_zero
  obtain ⟨t, ht⟩ := vertex_of_hatN_ne_zero hcl h1
  exact ⟨t, by rw [exteriorCellVertex_eq, ht, hw]⟩

theorem isWhitneyVertex_of_node {D : TriadicCube d} (hD : D ∈ whitneyCubes τ) {m : Fin d → ℤ}
    {w : Vec d} (hwD : w ∈ closedTriadicCube D) (hw : w = nodeN (D.scale - 1) m) :
    IsWhitneyVertex τ w := by
  obtain ⟨cell, hcell, hcl⟩ := exists_cell_of_mem_closedCube hD hwD
  subst hcell
  obtain ⟨j, hj⟩ := vertex_of_node_mem_closure hw hcl
  exact ⟨cell, j, hj⟩

end

end CoarseDeGiorgi.Whitney.Interpolation
