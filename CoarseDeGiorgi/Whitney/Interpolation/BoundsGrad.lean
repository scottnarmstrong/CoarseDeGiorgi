import CoarseDeGiorgi.Whitney.Interpolation.BoundsMain
import CoarseDeGiorgi.Statements.EuclidNorm

/-!
# Gradient bound for the Whitney interpolant (Lemma `l.whitney.interpolation`)
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset CoarseDeGiorgi

variable {d : ℕ} {τ : ℝ}

theorem grad_bound (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {M : ℝ}
    (hM : ∀ z z' : {z : Vec d // IsFreeVertex τ z},
      z.1 ∈ closedTriadicCube D → z'.1 ∈ closedTriadicCube D → |g z.1 - g z'.1| ≤ M)
    (cell : ExteriorCell d τ) (hcell : cell.1.val = D) {x : Vec d}
    (hx : x ∈ exteriorCellSet cell) :
    euclidNorm (smoothGrad g x) ≤ (3 * (d : ℝ)) / cubeScaleFactor D * M := by
  have hAg : AffClosed τ g := aff_closed_of_cont hg.2.1 hg.2.2.1
  obtain ⟨e, c, he⟩ := hAg cell
  have hgrad : ∀ i, smoothGrad g x i = e i :=
    smoothGrad_eq_of_affine (isOpen_exteriorCellSet cell) (fun y hy => he y (subset_closure hy)) hx
  have ht := cellT_pos cell
  have hcs : cubeScaleFactor D = 3 * cellT cell := by rw [← hcell]; exact cell_side cell
  have hinD : ∀ y ∈ closure (exteriorCellSet cell), y ∈ closedTriadicCube D := by
    intro y hy
    rw [← hcell]; exact closure_cell_subset_cube cell hy
  have hxD : x ∈ closedTriadicCube D := hinD x (subset_closure hx)
  have hM0 : 0 ≤ M := by
    have := diff_le hτ0 hτ1 hg hD hM hxD hxD
    linarith
  have hcoord : ∀ i, |e i| ≤ M / cellT cell := by
    intro i
    set j0 : Fin (d + 1) := ⟨(cell.2.2.symm i).val, by have := (cell.2.2.symm i).isLt; omega⟩
      with hj0
    set j1 : Fin (d + 1) := ⟨(cell.2.2.symm i).val + 1, by have := (cell.2.2.symm i).isLt; omega⟩
      with hj1
    have hv0 := cell_vertex_mem cell j0
    have hv1 := cell_vertex_mem cell j1
    have hdiff : g (exteriorCellVertex cell j1) - g (exteriorCellVertex cell j0) =
        -(cellT cell) * e i := by
      rw [he _ hv1, he _ hv0]
      have : vecDot e (exteriorCellVertex cell j1) - vecDot e (exteriorCellVertex cell j0) =
          -(cellT cell) * e i := by
        unfold vecDot
        rw [← Finset.sum_sub_distrib]
        have hk : ∀ k, e k * exteriorCellVertex cell j1 k - e k * exteriorCellVertex cell j0 k =
            e k * (if k = i then -(cellT cell) else 0) := by
          intro k
          rw [← mul_sub, cellVertex_eq, cellVertex_eq, hj0, hj1, kv_succ_sub]
        rw [Finset.sum_congr rfl (fun k _ => hk k)]
        simp [mul_comm]
      linarith
    have a1 := diff_le hτ0 hτ1 hg hD hM (hinD _ hv1) (hinD _ hv0)
    have a2 := diff_le hτ0 hτ1 hg hD hM (hinD _ hv0) (hinD _ hv1)
    rw [le_div_iff₀ ht]
    have h3 : |e i * cellT cell| ≤ M := by
      rw [abs_le]; constructor <;> linarith
    rwa [abs_mul, abs_of_pos ht] at h3
  have hB : 0 ≤ M / cellT cell := div_nonneg hM0 ht.le
  have hsum : vecNormSq (smoothGrad g x) ≤ ((d : ℝ) * (M / cellT cell)) ^ 2 := by
    unfold vecNormSq vecDot
    calc ∑ i, smoothGrad g x i * smoothGrad g x i
        ≤ ∑ _i : Fin d, (M / cellT cell) * (M / cellT cell) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hgrad i]
          have := hcoord i
          calc e i * e i = |e i| * |e i| := by rw [← abs_mul, abs_mul_self]
            _ ≤ _ := mul_self_le_mul_self (abs_nonneg _) this
      _ = (d : ℝ) * ((M / cellT cell) * (M / cellT cell)) := by simp
      _ ≤ ((d : ℝ) * (M / cellT cell)) ^ 2 := by
          have hd : (d : ℝ) ≤ (d : ℝ) * d := by exact_mod_cast Nat.le_mul_self d
          nlinarith [mul_nonneg hB hB]
  have hfin : euclidNorm (smoothGrad g x) ≤ (d : ℝ) * (M / cellT cell) := by
    unfold euclidNorm
    exact Real.sqrt_le_iff.2 ⟨by positivity, hsum⟩
  rw [hcs]
  calc euclidNorm (smoothGrad g x) ≤ (d : ℝ) * (M / cellT cell) := hfin
    _ = 3 * (d : ℝ) / (3 * cellT cell) * M := by field_simp

end CoarseDeGiorgi.WhitneyInterp
