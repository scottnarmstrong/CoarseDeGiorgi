import CoarseDeGiorgi.Whitney.Interpolation.BoundsCells

/-!
# Barycentric representation on Whitney cells; vertices in cubes
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset CoarseDeGiorgi

variable {d : ℕ} {τ : ℝ}

/-- `h` is affine on the closure of every Whitney simplex. -/
def AffClosed (τ : ℝ) (h : Vec d → ℝ) : Prop :=
  ∀ cell : ExteriorCell d τ, ∃ (e : Vec d) (c : ℝ),
    ∀ x ∈ closure (exteriorCellSet cell), h x = vecDot e x + c

theorem cell_bary (cell : ExteriorCell d τ) {x : Vec d} (hx : x ∈ closure (exteriorCellSet cell)) :
    ∃ l : Fin (d + 1) → ℝ, (∀ j, 0 ≤ l j) ∧ ∑ j, l j = 1 ∧
      (∀ h, AffClosed τ h → h x = ∑ j, l j * h (exteriorCellVertex cell j)) ∧
      ∀ j, l j ≠ 0 → ∀ i,
        ((cell.2.2.symm i).val < j.val → x i < exteriorCellCenter cell i + cellT cell / 2) ∧
          (¬ (cell.2.2.symm i).val < j.val → exteriorCellCenter cell i - cellT cell / 2 < x i) := by
  have hx' := hx
  rw [closure_cell] at hx'
  obtain ⟨l, h0, h1, h2, h3⟩ := bary (cellT_pos cell) hx'
  refine ⟨l, h0, h1, ?_, fun j hj i => h3 j i hj⟩
  intro h hh
  obtain ⟨e, c, he⟩ := hh cell
  rw [he x hx]
  have hv : ∀ j, h (exteriorCellVertex cell j) = vecDot e (exteriorCellVertex cell j) + c :=
    fun j => he _ (cell_vertex_mem cell j)
  simp only [hv]
  have hdot : vecDot e x = ∑ j, l j * vecDot e (exteriorCellVertex cell j) := by
    unfold vecDot
    simp only [h2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [cellVertex_eq]; ring
  rw [hdot]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h1]
  ring

theorem vertex_mem_cube (cell : ExteriorCell d τ) {x : Vec d}
    (hx : x ∈ closure (exteriorCellSet cell)) {j : Fin (d + 1)}
    (hs : ∀ i, ((cell.2.2.symm i).val < j.val → x i < exteriorCellCenter cell i + cellT cell / 2) ∧
          (¬ (cell.2.2.symm i).val < j.val → exteriorCellCenter cell i - cellT cell / 2 < x i))
    {D : TriadicCube d} (hDs : cell.1.val.scale - 1 ≤ D.scale) (hxD : x ∈ closedTriadicCube D) :
    exteriorCellVertex cell j ∈ closedTriadicCube D := by
  have hx' := hx
  rw [closure_cell] at hx'
  intro i
  have hxi := hxD i
  have hl : (D.scale : ℤ) = D.scale := rfl
  have hp : 0 < cubeScaleFactor D := by unfold cubeScaleFactor; positivity
  rw [abs_le] at hxi
  have hA : lat (cellT cell) (triadicCenter D i - cubeScaleFactor D / 2) := by
    refine lat_mono hDs ⟨D.index i, ?_⟩
    unfold triadicCenter cubeScaleFactor; ring
  have hB : lat (cellT cell) (triadicCenter D i + cubeScaleFactor D / 2) := by
    refine lat_mono hDs ⟨D.index i + 1, ?_⟩
    unfold triadicCenter cubeScaleFactor; push_cast; ring
  have key := box_coord (t := cellT cell) (zi := exteriorCellCenter cell i)
    (A := triadicCenter D i - cubeScaleFactor D / 2)
    (B := triadicCenter D i + cubeScaleFactor D / 2) (xi := x i)
    (c := if (cell.2.2.symm i).val < j.val then -(1 / 2 : ℝ) else 1 / 2)
    (cellT_pos cell) (cell_center_lat cell i) hA hB (by linarith [hxi.1]) (by linarith [hxi.2])
    ⟨by linarith [(hx'.1 i).1], by linarith [(hx'.1 i).2]⟩
    (by split_ifs <;> simp)
    (fun hc => by
      by_cases h : (cell.2.2.symm i).val < j.val
      · exact (hs i).1 h
      · rw [ite_eq_right h] at hc; norm_num at hc)
    (fun hc => by
      by_cases h : (cell.2.2.symm i).val < j.val
      · rw [ite_eq_left h] at hc; norm_num at hc
      · exact (hs i).2 h)
  have hv : exteriorCellVertex cell j i = exteriorCellCenter cell i + cellT cell *
      (if (cell.2.2.symm i).val < j.val then -(1 / 2 : ℝ) else 1 / 2) := rfl
  rw [← hv] at key
  rw [abs_le]
  constructor <;> linarith [key.1, key.2]

theorem vertex_of_lat (cell : ExteriorCell d τ) {w : Vec d}
    (hw : w ∈ closure (exteriorCellSet cell)) (hl : ∀ i, lat (cellT cell) (w i)) :
    ∃ j, exteriorCellVertex cell j = w := by
  rw [closure_cell] at hw
  obtain ⟨j, hj⟩ := exists_kv_of_lat (cellT_pos cell) hw (cell_center_lat cell) hl
  exact ⟨j, hj.symm⟩

theorem isFree_of_lat (w : Vec d)
    (hl : ∀ C : ExteriorCell d τ, w ∈ closure (exteriorCellSet C) → ∀ i, lat (cellT C) (w i))
    (hex : ∃ C : ExteriorCell d τ, w ∈ closure (exteriorCellSet C)) : IsFreeVertex τ w := by
  obtain ⟨C, hC⟩ := hex
  refine ⟨?_, fun cell hcell => vertex_of_lat cell hcell (hl cell hcell)⟩
  obtain ⟨j, hj⟩ := vertex_of_lat C hC (hl C hC)
  exact ⟨C, j, hj⟩

end CoarseDeGiorgi.WhitneyInterp
