import CoarseDeGiorgi.Statements.WhitneyCubesProperties
import CoarseDeGiorgi.Statements.IsFreeVertex
import CoarseDeGiorgi.Statements.IsWhitneyVertex
import CoarseDeGiorgi.Statements.ExteriorCellSet
import CoarseDeGiorgi.Statements.ExteriorCellVertex
import CoarseDeGiorgi.Statements.ExteriorCellCenter
import CoarseDeGiorgi.Statements.ExteriorCell
import CoarseDeGiorgi.Statements.WhitneyAdmissible
import CoarseDeGiorgi.Statements.FivefoldClosedTriadicCube
import CoarseDeGiorgi.Whitney.Interpolation.BoundsLattice

/-!
# Whitney cells as Kuhn simplices; covering and neighbouring cubes
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset CoarseDeGiorgi

variable {d : ℕ} {τ : ℝ}

/-- The side length of the Whitney simplices of the cell. -/
noncomputable def cellT (cell : ExteriorCell d τ) : ℝ := (3 : ℝ) ^ (cell.1.val.scale - 1)

theorem cellT_pos (cell : ExteriorCell d τ) : 0 < cellT cell := zpow_pos (by norm_num) _

theorem cube_side_eq (D : TriadicCube d) :
    cubeScaleFactor D = 3 * (3 : ℝ) ^ (D.scale - 1) := by
  unfold cubeScaleFactor
  rw [mul_comm, ← zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1; ring

theorem cell_side (cell : ExteriorCell d τ) : cubeScaleFactor cell.1.val = 3 * cellT cell :=
  cube_side_eq _

theorem closure_cell (cell : ExteriorCell d τ) :
    closure (exteriorCellSet cell) =
      closedKuhn (cellT cell) cell.2.2 (exteriorCellCenter cell) :=
  closure_simplex_eq _ _ _

theorem cellVertex_eq (cell : ExteriorCell d τ) (j : Fin (d + 1)) :
    exteriorCellVertex cell j = kv (cellT cell) cell.2.2 (exteriorCellCenter cell) j := rfl

theorem cell_center_lat (cell : ExteriorCell d τ) (i : Fin d) :
    ∃ k : ℤ, exteriorCellCenter cell i = cellT cell * k := by
  refine ⟨3 * cell.1.val.index i + (cell.2.1 i).val - 1, ?_⟩
  have h := cell_side cell
  unfold exteriorCellCenter triadicCenter
  simp only [cellT] at h ⊢
  rw [h]
  push_cast
  ring

theorem closure_cell_subset_cube (cell : ExteriorCell d τ) :
    closure (exteriorCellSet cell) ⊆ closedTriadicCube cell.1.val := by
  rw [closure_cell]
  intro x hx i
  have ht := cellT_pos cell
  have h1 := (hx.1 i)
  have hc : |((cell.2.1 i).val : ℝ) - 1| ≤ 1 := by
    have : (cell.2.1 i).val < 3 := (cell.2.1 i).isLt
    rw [abs_le]
    have h0 : (0 : ℝ) ≤ (cell.2.1 i).val := by positivity
    have h3 : ((cell.2.1 i).val : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp this
    constructor <;> linarith
  have hcs := cell_side cell
  have hx' : x i - triadicCenter cell.1.val i =
      (x i - exteriorCellCenter cell i) + cellT cell * (((cell.2.1 i).val : ℝ) - 1) := by
    unfold exteriorCellCenter
    simp only [cellT]
    ring
  show |x i - triadicCenter cell.1.val i| ≤ cubeScaleFactor cell.1.val / 2
  rw [hx', hcs]
  have h2 : |cellT cell * (((cell.2.1 i).val : ℝ) - 1)| ≤ cellT cell := by
    rw [abs_mul, abs_of_pos ht]
    calc cellT cell * |((cell.2.1 i).val : ℝ) - 1| ≤ cellT cell * 1 :=
          mul_le_mul_of_nonneg_left hc ht.le
      _ = cellT cell := mul_one _
  calc |x i - exteriorCellCenter cell i + cellT cell * (((cell.2.1 i).val : ℝ) - 1)|
      ≤ |x i - exteriorCellCenter cell i| + |cellT cell * (((cell.2.1 i).val : ℝ) - 1)| :=
        abs_add_le _ _
    _ ≤ 3 * cellT cell / 2 := by
        have : |x i - exteriorCellCenter cell i| ≤ cellT cell / 2 := by
          rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
        linarith

theorem closedTriadicCube_subset_ext {D : TriadicCube d} (hD : whitneyAdmissible τ D) :
    closedTriadicCube D ⊆ (closedReferenceCube (d := d) τ)ᶜ := by
  intro x hx hxr
  have hf : x ∈ fivefoldClosedTriadicCube D := by
    intro i
    have h := hx i
    have hp : 0 < cubeScaleFactor D := by unfold cubeScaleFactor; positivity
    linarith
  exact Set.disjoint_left.1 hD hf hxr

theorem cell_vertex_mem (cell : ExteriorCell d τ) (j : Fin (d + 1)) :
    exteriorCellVertex cell j ∈ closure (exteriorCellSet cell) := by
  rw [closure_cell, cellVertex_eq]
  exact kv_mem_closedKuhn _ (cellT_pos cell).le _ _ _

theorem cell_vertex_lat (cell : ExteriorCell d τ) (j : Fin (d + 1)) (i : Fin d) :
    lat (cellT cell) (exteriorCellVertex cell j i) := by
  obtain ⟨k, hk⟩ := cell_center_lat cell i
  rw [cellVertex_eq]
  simp only [kv, hk]
  split_ifs
  · exact ⟨k, by ring⟩
  · exact ⟨k + 1, by push_cast; ring⟩

/-- Every point of a closed cube is in the closure of a Whitney simplex of that cube. -/
theorem exists_cell_of_mem_cube {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ)
    {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    ∃ cell : ExteriorCell d τ, cell.1.val = D ∧ x ∈ closure (exteriorCellSet cell) := by
  classical
  set t : ℝ := (3 : ℝ) ^ (D.scale - 1) with ht
  have htp : 0 < t := zpow_pos (by norm_num) _
  have hs : cubeScaleFactor D = 3 * t := cube_side_eq D
  let c : Fin d → Fin 3 := fun i =>
    if x i - triadicCenter D i < -(t / 2) then ⟨0, by norm_num⟩
    else if t / 2 < x i - triadicCenter D i then ⟨2, by norm_num⟩ else ⟨1, by norm_num⟩
  let ctr : Vec d := fun i => triadicCenter D i + t * (((c i).val : ℝ) - 1)
  have hbd : ∀ i, -(t / 2) ≤ x i - ctr i ∧ x i - ctr i ≤ t / 2 := by
    intro i
    have h := hx i
    rw [hs] at h
    rw [abs_le] at h
    simp only [ctr, c]
    split_ifs with h1 h2
    · simp only [Nat.cast_zero]
      constructor <;> nlinarith [h.1, h.2]
    · simp only [Nat.cast_ofNat]
      constructor <;> nlinarith [h.1, h.2]
    · simp only [Nat.cast_one]
      constructor <;> nlinarith [not_lt.1 h1, not_lt.1 h2]
  let f : Fin d → ℝ := fun i => (x i - ctr i) / t + 1 / 2
  let π : Equiv.Perm (Fin d) := Tuple.sort f
  have hmono : Monotone (f ∘ π) := Tuple.monotone_sort f
  let cell : ExteriorCell d τ := (⟨D, hD⟩, (c, π))
  have hcenter : exteriorCellCenter cell = ctr := by
    funext i; rfl
  refine ⟨cell, rfl, ?_⟩
  rw [closure_cell, hcenter]
  refine ⟨hbd, fun a b hab => ?_⟩
  have := hmono hab.le
  simp only [Function.comp, f] at this
  have h2 : (x (π a) - ctr (π a)) / t ≤ (x (π b) - ctr (π b)) / t := by linarith
  exact (div_le_div_iff_of_pos_right htp).1 h2

/-- Neighbouring selected cubes have comparable sizes. -/
theorem scale_le_succ (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D E : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) (hE : E ∈ whitneyCubes (d := d) τ) {x : Vec d}
    (hxD : x ∈ closedTriadicCube D) (hxE : x ∈ closedTriadicCube E) :
    E.scale ≤ D.scale + 1 := by
  obtain ⟨-, -, -, h4⟩ := CoarseDeGiorgi.whitney_cubes (d := d) (τ := τ) hτ0 hτ1
  have hE' := h4 E hE x hxE
  have hD' := h4 D hD x hxD
  have hlt : 2 * cubeScaleFactor E < 9 * cubeScaleFactor D :=
    lt_of_lt_of_le hE'.1 (hE'.2.1.trans hD'.2.2)
  by_contra hcon
  push Not at hcon
  have hp : 0 < cubeScaleFactor D := by unfold cubeScaleFactor; positivity
  have h9 : 9 * cubeScaleFactor D ≤ cubeScaleFactor E := by
    unfold cubeScaleFactor
    have : (3 : ℝ) ^ (D.scale + 2) ≤ 3 ^ E.scale :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_add₀ (by norm_num)] at this
    norm_num at this
    linarith
  have hE0 : 0 < cubeScaleFactor E := by unfold cubeScaleFactor; positivity
  linarith

end CoarseDeGiorgi.WhitneyInterp
