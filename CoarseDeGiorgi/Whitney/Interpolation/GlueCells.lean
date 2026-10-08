module

public import CoarseDeGiorgi.Whitney.Interpolation.GlueCells0

/-! # Kuhn cells of mesh `3^n`

Transport of the level-zero cell facts along the dilation `dil n`. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Interpolation

open Homogenization

noncomputable section

variable {d : ℕ}

/-- The open Kuhn cell of mesh `3^n` with center `3^n q` and coordinate order `π`. -/
abbrev cellN (n : ℤ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) : Set (Vec d) :=
  Foundations.Simplex.kuhnSimplex n π (fun i => (3 : ℝ) ^ n * (q i : ℝ))

theorem dil_apply (n : ℤ) (x : Vec d) (i : Fin d) : dil n x i = (3 : ℝ) ^ (-n) * x i := rfl

theorem three_zpow_mul_neg (n : ℤ) : (3 : ℝ) ^ n * (3 : ℝ) ^ (-n) = 1 := by
  rw [← zpow_add₀ (by norm_num)]; simp

theorem three_zpow_neg_mul (n : ℤ) : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ n = 1 := by
  rw [mul_comm]; exact three_zpow_mul_neg n

theorem smul_dil (n : ℤ) (x : Vec d) : (3 : ℝ) ^ n • dil n x = x := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, dil_apply]
  rw [← mul_assoc, three_zpow_mul_neg, one_mul]

theorem dil_smul (n : ℤ) (y : Vec d) : dil n ((3 : ℝ) ^ n • y) = y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, dil_apply]
  rw [← mul_assoc, three_zpow_neg_mul, one_mul]

theorem nodeN_eq_smul (n : ℤ) (m : Fin d → ℤ) : nodeN n m = (3 : ℝ) ^ n • seedNode 0 m := by
  rw [← dil_nodeN n m, smul_dil]

theorem mem_cellN_iff {n : ℤ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)} {x : Vec d} :
    x ∈ cellN n q π ↔ dil n x ∈ cell0 q π := by
  rw [mem_cell0_iff]
  simp only [Foundations.Simplex.kuhnSimplex, Foundations.Simplex.simplexCube,
    Set.mem_ofPred_eq, dil_apply]
  have hp := pos_zpow3 n
  have hq := pos_zpow3 (-n)
  have key : ∀ a : Fin d, (3 : ℝ) ^ (-n) * x a - q a =
      (3 : ℝ) ^ (-n) * (x a - (3 : ℝ) ^ n * q a) := by
    intro a
    have := three_zpow_neg_mul n
    linear_combination (q a : ℝ) * this
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [key]
      have := h1 i
      constructor <;> nlinarith [this.1, this.2, three_zpow_neg_mul n]
    · show (3 : ℝ) ^ (-n) * x (π i) - q (π i) < (3 : ℝ) ^ (-n) * x (π j) - q (π j)
      rw [key, key]
      exact mul_lt_mul_of_pos_left (h2 hij) hq
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · have := h1 i
      rw [key] at this
      constructor <;> nlinarith [this.1, this.2, three_zpow_mul_neg n]
    · have := h2 hij
      change (3 : ℝ) ^ (-n) * x (π i) - q (π i) < (3 : ℝ) ^ (-n) * x (π j) - q (π j) at this
      rw [key, key] at this
      exact lt_of_mul_lt_mul_left this hq.le

theorem dil_mem_closure {n : ℤ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)} {x : Vec d}
    (hx : x ∈ closure (cellN n q π)) : dil n x ∈ closure (cell0 q π) :=
  map_mem_closure (by unfold dil; fun_prop) hx (fun _ h => mem_cellN_iff.mp h)

theorem smul_mem_closure {n : ℤ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)} {y : Vec d}
    (hy : y ∈ closure (cell0 q π)) : (3 : ℝ) ^ n • y ∈ closure (cellN n q π) :=
  map_mem_closure (by fun_prop) hy (fun z hz => by
    rw [mem_cellN_iff, dil_smul]; exact hz)

theorem nodeN_vertex_mem_closure (n : ℤ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (t : Fin (d + 1)) : nodeN n (seedKuhnVertexIndex q π t) ∈ closure (cellN n q π) := by
  rw [nodeN_eq_smul]
  exact smul_mem_closure (seedNode_vertex_mem_closure q π t)

theorem hatN_eq_zero_of_not_vertex {n : ℤ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {m : Fin d → ℤ} (hm : m ∉ Set.range (seedKuhnVertexIndex q π)) {x : Vec d}
    (hx : x ∈ closure (cellN n q π)) : hatN n m x = 0 := by
  have hcl : IsClosed {y : Vec d | seedHat 0 m y = 0} :=
    isClosed_eq (by unfold seedHat; exact continuous_nodalHat _ _) continuous_const
  have hsub : cell0 q π ⊆ {y : Vec d | seedHat 0 m y = 0} := fun y hy =>
    seedHat_zero_off_kuhnVertices hy hm
  exact hcl.closure_subset_iff.mpr hsub (dil_mem_closure hx)

theorem vertex_of_hatN_ne_zero {n : ℤ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {m : Fin d → ℤ} {x : Vec d} (hx : x ∈ closure (cellN n q π)) (h : hatN n m x ≠ 0) :
    m ∈ Set.range (seedKuhnVertexIndex q π) := by
  by_contra hm
  exact h (hatN_eq_zero_of_not_vertex hm hx)

theorem interpP_on_cell {n : ℤ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)} {x : Vec d}
    (hx : x ∈ cellN n q π) (f : Vec d → ℝ) :
    interpP n f x = seedKuhnAffine 0 q π (fun m => f (nodeN n m)) (dil n x) :=
  seedWeightedHat_eq_affine (mem_cellN_iff.mp hx) _

/-- On a cell the interpolant is an affine function. -/
theorem interpP_affine (n : ℤ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (f : Vec d → ℝ) :
    ∃ (e : Vec d) (c : ℝ), ∀ x ∈ cellN n q π, interpP n f x = vecDot e x + c := by
  set c : (Fin d → ℤ) → ℝ := fun m => f (nodeN n m)
  set δ : Fin d → ℝ := fun i => c (seedKuhnVertexIndex q π i.castSucc) -
    c (seedKuhnVertexIndex q π i.succ) with hδ
  refine ⟨fun j => (3 : ℝ) ^ (-n) * δ (π.symm j),
    c (seedKuhnVertexIndex q π (Fin.last d)) + ∑ i : Fin d, δ i * (1 / 2 - q (π i)), ?_⟩
  intro x hx
  rw [interpP_on_cell hx]
  unfold seedKuhnAffine
  have h1 : vecDot (fun j => (3 : ℝ) ^ (-n) * δ (π.symm j)) x =
      ∑ i : Fin d, (3 : ℝ) ^ (-n) * δ i * x (π i) := by
    unfold vecDot
    rw [← Equiv.sum_comp π]
    simp
  have hs : ∑ i : Fin d, δ i * seedUnitCoordinate 0 q π (dil n x) i =
      ∑ i : Fin d, ((3 : ℝ) ^ (-n) * δ i * x (π i) + δ i * (1 / 2 - q (π i))) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [seedUnitCoordinate, seedScale_zero, dil_apply]
    ring
  rw [Finset.sum_add_distrib] at hs
  show c (seedKuhnVertexIndex q π (Fin.last d)) + ∑ i : Fin d,
    δ i * seedUnitCoordinate 0 q π (dil n x) i = _
  rw [h1, hs]
  ring

theorem vecDot_continuous (e : Vec d) : Continuous fun x => vecDot e x := by
  unfold vecDot; fun_prop

/-- A function that is affine on a cell and continuous on its closure is the interpolant of its
node values there. -/
theorem eq_interpP_on_closure {n : ℤ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)} {g : Vec d → ℝ}
    {e : Vec d} {c : ℝ} (hg : ∀ x ∈ cellN n q π, g x = vecDot e x + c)
    (hc : ContinuousOn g (closure (cellN n q π))) :
    ∀ x ∈ closure (cellN n q π), g x = interpP n g x := by
  have hcl : Set.EqOn g (fun x => vecDot e x + c) (closure (cellN n q π)) :=
    Set.EqOn.of_subset_closure hg hc ((vecDot_continuous e).add continuous_const).continuousOn
      subset_closure subset_rfl
  let ℓ : Vec d →ₗ[ℝ] ℝ :=
    { toFun := fun y => vecDot e ((3 : ℝ) ^ n • y)
      map_add' := fun y z => by rw [smul_add, vecDot_add_right]
      map_smul' := fun a y => by
        simp only [vecDot_smul_right, RingHom.id_apply, smul_eq_mul]; ring }
  let L : Vec d →ᵃ[ℝ] ℝ := ℓ.toAffineMap + AffineMap.const ℝ (Vec d) c
  have hL : ∀ y, L y = vecDot e ((3 : ℝ) ^ n • y) + c := fun y => rfl
  have hvert : ∀ t : Fin (d + 1), L (seedNode 0 (seedKuhnVertexIndex q π t)) =
      g (nodeN n (seedKuhnVertexIndex q π t)) := by
    intro t
    rw [hL, ← nodeN_eq_smul]
    exact (hcl (nodeN_vertex_mem_closure n q π t)).symm
  have hLeq := affineMap_eq_seedKuhnAffine q π (fun m => g (nodeN n m)) L hvert
  have hopen : ∀ x ∈ cellN n q π, g x = interpP n g x := by
    intro x hx
    rw [interpP_on_cell hx, ← hLeq, hL, smul_dil, hg x hx]
  exact Set.EqOn.of_subset_closure hopen hc (continuous_interpP n g).continuousOn
    subset_closure subset_rfl

end

end CoarseDeGiorgi.Whitney.Interpolation
