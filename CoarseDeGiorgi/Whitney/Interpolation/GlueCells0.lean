import CoarseDeGiorgi.Whitney.Interpolation.Basic
import CoarseDeGiorgi.Whitney.SeedClosedCover

/-! # Level-zero Kuhn cells: vertices, closure, barycentric reproduction of affine maps -/

namespace CoarseDeGiorgi.Whitney.Interpolation

open Homogenization

noncomputable section

variable {d : ℕ}

/-- The open Kuhn cell of mesh `1` with center `q` and coordinate order `π`. -/
abbrev cell0 (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) : Set (Vec d) :=
  Foundations.Simplex.kuhnSimplex (-((0 : ℕ) : ℤ)) π (fun i => seedScale 0 * (q i : ℝ))

theorem mem_cell0_iff {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)} {y : Vec d} :
    y ∈ cell0 q π ↔ (∀ i, -(1 / 2 : ℝ) < y i - q i ∧ y i - q i < 1 / 2) ∧
      StrictMono fun i => y (π i) - q (π i) := by
  simp only [Foundations.Simplex.kuhnSimplex, Foundations.Simplex.simplexCube, seedScale_zero,
    Set.mem_ofPred_eq, Nat.cast_zero, neg_zero, zpow_zero, one_mul]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun i => ?_, h2⟩ <;> specialize h1 i <;>
    constructor <;> linarith [h1.1, h1.2]

/-- A coordinate strictly inside `(-1/2, 1/2)`, strictly increasing in the index. -/
def interiorCoord (i : Fin d) : ℝ := -(1 / 2 : ℝ) + ((i.val : ℝ) + 1) / ((d : ℝ) + 1)

theorem interiorCoord_bounds (i : Fin d) :
    -(1 / 2 : ℝ) < interiorCoord i ∧ interiorCoord i < 1 / 2 := by
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
  have hn1 : (i.val : ℝ) + 1 < (d : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ i.isLt
  have h0 : 0 < ((i.val : ℝ) + 1) / ((d : ℝ) + 1) := div_pos hn0 hd
  have h1 : ((i.val : ℝ) + 1) / ((d : ℝ) + 1) < 1 := (div_lt_one hd).2 hn1
  constructor <;> dsimp [interiorCoord] <;> linarith

theorem interiorCoord_strict {i j : Fin d} (hij : i < j) : interiorCoord i < interiorCoord j := by
  have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hnum : (i.val : ℝ) + 1 < (j.val : ℝ) + 1 := by linarith
  unfold interiorCoord
  exact (add_lt_add_iff_left (-(1 / 2 : ℝ))).2 (div_lt_div_of_pos_right hnum hd)

/-- A path from a Kuhn vertex (at `ε = 0`) into the interior of the cell. -/
def vertexPath (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (t : Fin (d + 1)) (ε : ℝ) : Vec d :=
  fun i => (q i : ℝ) + (1 - ε) * (if (π.symm i).val < t.val then -(1 / 2 : ℝ) else 1 / 2) +
    ε * interiorCoord (π.symm i)

theorem continuous_vertexPath (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (t : Fin (d + 1)) :
    Continuous (vertexPath q π t) := by
  unfold vertexPath
  fun_prop

theorem vertexPath_mem (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (t : Fin (d + 1)) {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε < 1) : vertexPath q π t ε ∈ cell0 q π := by
  rw [mem_cell0_iff]
  constructor
  · intro i
    let v : ℝ := if (π.symm i).val < t.val then -(1 / 2 : ℝ) else 1 / 2
    have hv₀ : -(1 / 2 : ℝ) ≤ v := by dsimp [v]; split_ifs <;> norm_num
    have hv₁ : v ≤ 1 / 2 := by dsimp [v]; split_ifs <;> norm_num
    have hw := interiorCoord_bounds (π.symm i)
    have hweight : 0 ≤ 1 - ε := by linarith
    have hlo := mul_le_mul_of_nonneg_left hv₀ hweight
    have hwlo := mul_lt_mul_of_pos_left hw.1 hε₀
    have hhi := mul_le_mul_of_nonneg_left hv₁ hweight
    have hwhi := mul_lt_mul_of_pos_left hw.2 hε₀
    simp only [vertexPath]
    constructor <;> nlinarith
  · intro i j hij
    have hstep : (if i.val < t.val then -(1 / 2 : ℝ) else 1 / 2) ≤
        (if j.val < t.val then -(1 / 2 : ℝ) else 1 / 2) := by
      by_cases hi : i.val < t.val
      · by_cases hj : j.val < t.val <;> simp [hi, hj]
      · have hj : ¬ j.val < t.val := by have := Fin.lt_def.mp hij; omega
        simp [hi, hj]
    have hlinear := interiorCoord_strict hij
    have hweight : 0 ≤ 1 - ε := by linarith
    have hstep' := mul_le_mul_of_nonneg_left hstep hweight
    have hlinear' := mul_lt_mul_of_pos_left hlinear hε₀
    have := add_lt_add_of_le_of_lt hstep' hlinear'
    simp only [vertexPath, π.symm_apply_apply]
    linarith

theorem vertexPath_zero (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (t : Fin (d + 1)) :
    vertexPath q π t 0 = seedNode 0 (seedKuhnVertexIndex q π t) := by
  funext i
  simp only [vertexPath, seedNode, seedScale_zero, seedKuhnVertexIndex]
  split_ifs <;> push_cast <;> ring

theorem seedNode_vertex_mem_closure (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (t : Fin (d + 1)) :
    seedNode 0 (seedKuhnVertexIndex q π t) ∈ closure (cell0 q π) := by
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    norm_num
  have himage : vertexPath q π t 0 ∈ closure ((vertexPath q π t) '' Set.Ioo (0 : ℝ) 1) :=
    mem_closure_image (continuous_vertexPath q π t).continuousAt hzero
  have hsubset : (vertexPath q π t) '' Set.Ioo (0 : ℝ) 1 ⊆ cell0 q π := by
    rintro x ⟨ε, hε, rfl⟩
    exact vertexPath_mem q π t hε.1 hε.2
  rw [← vertexPath_zero]
  exact closure_mono hsubset himage

theorem seedNode_vertex_step (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (i : Fin d) :
    seedNode 0 (seedKuhnVertexIndex q π i.castSucc) - seedNode 0 (seedKuhnVertexIndex q π i.succ) =
      fun a => if a = π i then 1 else 0 := by
  funext a
  simp only [Pi.sub_apply, seedNode, seedScale_zero]
  by_cases ha : a = π i
  · subst a
    simp only [seedKuhnVertexIndex, Equiv.symm_apply_apply, Fin.val_castSucc, Fin.val_succ]
    have hlt : i.val < i.val + 1 := by omega
    simp only [lt_self_iff_false, hlt, ↓reduceIte]
    push_cast
    ring
  · have hrank : (π.symm a).val ≠ i.val := by
      intro h
      apply ha
      calc
        a = π (π.symm a) := by simp
        _ = π i := by rw [Fin.ext h]
    have hcond : ((π.symm a).val < i.val) ↔ ((π.symm a).val < i.val + 1) := by omega
    simp only [seedKuhnVertexIndex, Fin.val_castSucc, Fin.val_succ]
    rw [if_congr hcond rfl rfl]
    simp [ha]

theorem seedNode_vertex_last (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (a : Fin d) :
    seedNode 0 (seedKuhnVertexIndex q π (Fin.last d)) a = (q a : ℝ) - 1 / 2 := by
  have hlt : (π.symm a).val < d := (π.symm a).isLt
  simp only [seedNode, seedScale_zero, seedKuhnVertexIndex, Fin.val_last]
  rw [ite_eq_left hlt]
  push_cast
  ring

theorem coordinate_decomposition (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (x : Vec d) :
    x - seedNode 0 (seedKuhnVertexIndex q π (Fin.last d)) =
      ∑ i : Fin d, seedUnitCoordinate 0 q π x i •
        (seedNode 0 (seedKuhnVertexIndex q π i.castSucc) -
          seedNode 0 (seedKuhnVertexIndex q π i.succ)) := by
  classical
  ext a
  let j : Fin d := π.symm a
  rw [Pi.sub_apply, seedNode_vertex_last]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, seedNode_vertex_step]
  rw [Finset.sum_eq_single j]
  · have hja : a = π j := by simp [j]
    simp only [ite_eq_left hja]
    simp only [seedUnitCoordinate, j, π.apply_symm_apply, seedScale_zero]
    ring
  · intro i hi hne
    have hai : a ≠ π i := by
      intro h
      apply hne
      calc
        i = π.symm (π i) := by simp
        _ = π.symm a := by rw [h]
        _ = j := rfl
    simp [hai]
  · simp

/-- An affine map with prescribed vertex values is the seed Kuhn interpolant. -/
theorem affineMap_eq_seedKuhnAffine (q : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (c : (Fin d → ℤ) → ℝ) (L : Vec d →ᵃ[ℝ] ℝ)
    (hvalues : ∀ t : Fin (d + 1),
      L (seedNode 0 (seedKuhnVertexIndex q π t)) = c (seedKuhnVertexIndex q π t)) (x : Vec d) :
    L x = seedKuhnAffine 0 q π c x := by
  let v := seedNode 0 (seedKuhnVertexIndex q π (Fin.last d))
  have hdecomp := coordinate_decomposition q π x
  calc
    L x = L ((x -ᵥ v) +ᵥ v) := by
      congr 1
      exact (vsub_vadd x v).symm
    _ = L.linear (x -ᵥ v) +ᵥ L v := L.map_vadd v (x -ᵥ v)
    _ = seedKuhnAffine 0 q π c x := by
      change L.linear (x - seedNode 0 (seedKuhnVertexIndex q π (Fin.last d))) +
          L (seedNode 0 (seedKuhnVertexIndex q π (Fin.last d))) = _
      rw [hdecomp]
      have hstep (i : Fin d) :
          L.linear (seedNode 0 (seedKuhnVertexIndex q π i.castSucc) -
            seedNode 0 (seedKuhnVertexIndex q π i.succ)) =
            c (seedKuhnVertexIndex q π i.castSucc) - c (seedKuhnVertexIndex q π i.succ) := by
        change L.linear (seedNode 0 (seedKuhnVertexIndex q π i.castSucc) -ᵥ
            seedNode 0 (seedKuhnVertexIndex q π i.succ)) = _
        rw [L.linearMap_vsub, hvalues, hvalues]
        simp only [vsub_eq_sub]
      simp only [map_sum, map_smul, hstep, hvalues, smul_eq_mul]
      unfold seedKuhnAffine
      have hsum : (∑ i : Fin d, seedUnitCoordinate 0 q π x i *
            (c (seedKuhnVertexIndex q π i.castSucc) - c (seedKuhnVertexIndex q π i.succ))) =
            ∑ i : Fin d, (c (seedKuhnVertexIndex q π i.castSucc) -
                c (seedKuhnVertexIndex q π i.succ)) * seedUnitCoordinate 0 q π x i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      ring

end

end CoarseDeGiorgi.Whitney.Interpolation
