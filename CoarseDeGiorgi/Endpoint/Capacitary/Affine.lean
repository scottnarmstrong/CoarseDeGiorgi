module

public import CoarseDeGiorgi.Endpoint.Capacitary.Seed
public import CoarseDeGiorgi.Weighted.Lipschitz
public import CoarseDeGiorgi.Weighted.TestingCompactSupport
public import CoarseDeGiorgi.Moments.Cells

/-! Affine data of the fixed capacitary seed on level-four simplices. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Set Topology
open CoarseDeGiorgi.Whitney
open scoped BigOperators

variable {d : ℕ}

noncomputable def capacitaryCoefficient (d : ℕ) (m : Fin d → ℤ) : ℝ :=
  if m ∈ capacitaryNodes d then 1 else 0

noncomputable def capacitaryDifference (η : SimplexIndex d 4) (i : Fin d) : ℝ :=
  capacitaryCoefficient d (seedKuhnVertexIndex η.val.1 η.val.2 i.castSucc) -
    capacitaryCoefficient d (seedKuhnVertexIndex η.val.1 η.val.2 i.succ)

noncomputable def capacitaryDirection (η : SimplexIndex d 4) : Vec d :=
  fun j => 81 * capacitaryDifference η (η.val.2.symm j)

noncomputable def capacitaryConstant (η : SimplexIndex d 4) : ℝ :=
  capacitaryCoefficient d (seedKuhnVertexIndex η.val.1 η.val.2 (Fin.last d)) +
    ∑ i : Fin d, capacitaryDifference η i * (1 / 2 - (η.val.1 (η.val.2 i) : ℝ))

theorem capacitarySeed_affine (η : SimplexIndex d 4) {x : Vec d}
    (hx : x ∈ simplexCell 4 η) :
    capacitarySeed d x = vecDot (capacitaryDirection η) x + capacitaryConstant η := by
  classical
  have hx' : x ∈ Foundations.Simplex.kuhnSimplex (-(4 : ℕ) : ℤ) η.val.2
      (fun i => seedScale 4 * (η.val.1 i : ℝ)) := by
    simpa only [simplexCell, Moments.simplex_eq_kuhnSimplex, seedScale] using hx
  rw [capacitarySeed_eq_interpolation]
  change (∑' m, capacitaryCoefficient d m * seedHat 4 m x) = _
  rw [seedWeightedHat_eq_affine hx']
  have hdot : vecDot (capacitaryDirection η) x =
      ∑ i : Fin d, 81 * capacitaryDifference η i * x (η.val.2 i) := by
    unfold vecDot capacitaryDirection
    rw [← Equiv.sum_comp η.val.2]
    simp only [Equiv.symm_apply_apply]
  have hs : ∑ i : Fin d, capacitaryDifference η i *
      seedUnitCoordinate 4 η.val.1 η.val.2 x i =
      ∑ i : Fin d, (81 * capacitaryDifference η i * x (η.val.2 i) +
        capacitaryDifference η i * (1 / 2 - (η.val.1 (η.val.2 i) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro i _
    norm_num only [seedUnitCoordinate, seedScale, zpow_neg, zpow_natCast, pow_succ,
      pow_zero]
    ring
  rw [Finset.sum_add_distrib] at hs
  change _ + (∑ i : Fin d, capacitaryDifference η i *
    seedUnitCoordinate 4 η.val.1 η.val.2 x i) = _
  rw [hdot, hs]
  unfold capacitaryConstant
  ring

theorem capacitaryDirection_bound (η : SimplexIndex d 4) :
    vecDot (capacitaryDirection η) (capacitaryDirection η) ≤ (d : ℝ) * 81 ^ 2 := by
  classical
  have hc (m : Fin d → ℤ) : 0 ≤ capacitaryCoefficient d m ∧ capacitaryCoefficient d m ≤ 1 := by
    unfold capacitaryCoefficient
    split_ifs <;> norm_num
  have hi (i : Fin d) : (capacitaryDirection η i) ^ 2 ≤ (81 : ℝ) ^ 2 := by
    have h1 := hc (seedKuhnVertexIndex η.val.1 η.val.2 (η.val.2.symm i).castSucc)
    have h2 := hc (seedKuhnVertexIndex η.val.1 η.val.2 (η.val.2.symm i).succ)
    change (81 * (_ - _)) ^ 2 ≤ _
    have hd : |capacitaryDifference η (η.val.2.symm i)| ≤ 1 := by
      rw [abs_le]
      constructor <;> dsimp only [capacitaryDifference] <;> linarith only [h1.1, h1.2, h2.1, h2.2]
    have hsq := sq_le_sq₀ (abs_nonneg _) zero_le_one |>.mpr hd
    rw [sq_abs] at hsq
    change (81 * capacitaryDifference η (η.val.2.symm i)) ^ 2 ≤ _
    nlinarith only [hsq]
  unfold vecDot
  calc
    _ = ∑ i : Fin d, (capacitaryDirection η i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ _i : Fin d, (81 : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp

theorem capacitarySeed_memH1a0 [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) :
    MemH1a0 a (originCube 1) (capacitarySeed d) (smoothGrad (capacitarySeed d)) := by
  have hV := originCube_domain (d := d) one_pos
  have hne := originCube_nonempty (d := d) one_pos
  have hm := Weighted.memH1a_of_lipschitzOn hV hne ha
    capacitarySeed_lipschitz.lipschitzOnWith EventuallyEq.rfl
  have hs := capacitarySeed_support (d := d)
  refine Weighted.MemH1a.memH1a0_of_compact_support hV hne ha hm hs.1 hs.2 ?_
  exact Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx

/-- Classical gradient of an affine datum, including its constant offset. -/
theorem capacitary_smoothGrad_affine (e : Vec d) (c : ℝ) (x : Vec d) :
    smoothGrad (fun y => vecDot e y + c) x = e := by
  funext i
  change (fderiv ℝ (fun y => Weighted.responseAffine e y + c) x) (basisVec i) = e i
  rw [((Weighted.responseAffine e).hasFDerivAt.add_const c).fderiv]
  exact vecDot_basisVec_right e i

/-- The nodal seed has its affine cell gradient at every interior point. -/
theorem capacitarySeed_gradient (η : SimplexIndex d 4) {x : Vec d}
    (hx : x ∈ simplexCell 4 η) : smoothGrad (capacitarySeed d) x = capacitaryDirection η := by
  have heq : capacitarySeed d =ᶠ[𝓝 x]
      (fun y => vecDot (capacitaryDirection η) y + capacitaryConstant η) := by
    filter_upwards [(simplexCell_isOpenBoundedConvexDomain 4 η).isOpen.mem_nhds hx] with y hy
    exact capacitarySeed_affine η hy
  have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq
  have hgrad : smoothGrad (capacitarySeed d) x =
      smoothGrad (fun y => vecDot (capacitaryDirection η) y + capacitaryConstant η) x := by
    funext i
    exact congrArg (fun T : Vec d →L[ℝ] ℝ => T (basisVec i)) hd
  exact hgrad.trans (capacitary_smoothGrad_affine _ _ _)

/-- Any cell meeting the obstacle has constant-one affine datum. -/
theorem capacitary_cell_meets_obstacle (η : SimplexIndex d 4)
    (hx : (simplexCell 4 η ∩ remoteCube d (1 / 2)).Nonempty) :
    capacitaryDirection η = 0 ∧ capacitaryConstant η = 1 := by
  obtain ⟨x, hxcell, hxQ⟩ := hx
  have heq : capacitarySeed d =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [(remoteCube_domain (by norm_num : (0 : ℝ) < 1 / 2)).isOpen.mem_nhds hxQ]
      with y hy
    exact capacitarySeed_eq_one hy
  have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq
  have hzero : smoothGrad (capacitarySeed d) x = 0 := by
    funext i
    change (fderiv ℝ (capacitarySeed d) x) (basisVec i) = 0
    rw [hd, (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).fderiv]
    rfl
  have he : capacitaryDirection η = 0 := (capacitarySeed_gradient η hxcell).symm.trans hzero
  refine ⟨he, ?_⟩
  have h := capacitarySeed_affine η hxcell
  rw [capacitarySeed_eq_one hxQ, he, vecDot_zero_left, zero_add] at h
  exact h.symm

end CoarseDeGiorgi.Endpoint
