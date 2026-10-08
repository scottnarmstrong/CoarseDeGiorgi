module

public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import CoarseDeGiorgi.Statements.BesovCubeNorm
public import CoarseDeGiorgi.SharpnessExamples.CylinderFiniteMeans

/-! # Triadic cubes as unions of Kuhn simplices

The cube `z + □_{-k}` of the cube quasi-norm is the union, up to a null set, of the `d!` simplices
of the triangulation with the same offset, so its average is the mean of their averages.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

open CoarseDeGiorgi.Foundations.Simplex

/-- The centre `3^{-k} z` of the triadic cube with index `j`. -/
noncomputable def triadicCentre {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Vec d :=
  fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)

/-- The triadic cube of side `3^{-k}` used in `besovCubeNorm`. -/
def triadicCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Set (Vec d) :=
  {x : Vec d | x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) ∈
    originCube ((3 : ℝ) ^ (-(k : ℤ)))}

theorem triadicCube_eq {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    triadicCube k j = simplexCube (-(k : ℤ)) (triadicCentre k j) := by
  ext x
  simp only [triadicCube, triadicCentre, Set.mem_ofPred_eq, originCube, Pi.sub_apply, simplexCube,
    neg_div]

theorem simplexCell_eq_kuhn {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    simplexCell k η = kuhnSimplex (-(k : ℤ)) η.1.2
      (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.1.1 i : ℝ)) := by
  unfold simplexCell
  exact CoarseDeGiorgi.Moments.simplex_eq_kuhnSimplex _ _ _

theorem volume_triadicCube_toReal {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    (volume (triadicCube k j)).toReal = (3 : ℝ) ^ (-(k : ℤ) * (d : ℤ)) := by
  rw [triadicCube_eq, volume_simplexCube, ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le]

/-- The average over a triadic cube is the mean of the averages over its `d!` simplices. -/
theorem volumeAverage_triadicCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) {w : Vec d → ℝ}
    (hw : IntegrableOn w (triadicCube k j) volume) :
    volumeAverage (triadicCube k j) w =
      (d.factorial : ℝ)⁻¹ * ∑ π : Equiv.Perm (Fin d),
        volumeAverage (kuhnSimplex (-(k : ℤ)) π (triadicCentre k j)) w := by
  set n : ℤ := -(k : ℤ) with hn
  set c := triadicCentre k j with hc
  have hQ : triadicCube k j = simplexCube n c := triadicCube_eq k j
  have hmeas : ∀ π : Equiv.Perm (Fin d), MeasurableSet (kuhnSimplex n π c) :=
    fun π => (isOpen_kuhnSimplex n π c).measurableSet
  have hsub : ∀ π : Equiv.Perm (Fin d), kuhnSimplex n π c ⊆ triadicCube k j := by
    intro π; rw [hQ]; exact kuhnSimplex_subset_cube n π c
  have hint : ∫ x in triadicCube k j, w x = ∑ π : Equiv.Perm (Fin d),
      ∫ x in kuhnSimplex n π c, w x := by
    rw [hQ, setIntegral_congr_set (iUnion_kuhnSimplex_ae_eq_cube n c).symm,
      integral_iUnion_fintype hmeas (pairwise_disjoint_kuhnSimplex n c)]
    intro π
    exact hw.mono_set (hsub π)
  have hV : (volume (triadicCube k j)).toReal = (3 : ℝ) ^ (n * (d : ℤ)) :=
    volume_triadicCube_toReal k j
  have hT : ∀ π : Equiv.Perm (Fin d), (volume (kuhnSimplex n π c)).toReal =
      (3 : ℝ) ^ (n * (d : ℤ)) / (d.factorial : ℝ) := by
    intro π
    rw [volume_kuhnSimplex, ENNReal.toReal_div, ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le,
      ENNReal.toReal_natCast]
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hpos : (3 : ℝ) ^ (n * (d : ℤ)) ≠ 0 := (zpow_pos (by norm_num) _).ne'
  unfold volumeAverage
  rw [hint, hV]
  simp_rw [hT]
  rw [← Finset.mul_sum]
  field_simp

theorem mem_triangulation_of_perm {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k))
    (π : Equiv.Perm (Fin d)) : (gridOffset k j, π) ∈ (triangulation (d := d) k) := by
  classical
  unfold triangulation
  exact Finset.mem_image.mpr ⟨(j, π), Finset.mem_univ _, rfl⟩

/-- The simplex of the triangulation with offset `j` and permutation `π`. -/
theorem kuhn_eq_simplexCell {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) :
    kuhnSimplex (-(k : ℤ)) π (triadicCentre k j) =
      simplexCell k (⟨(gridOffset k j, π), mem_triangulation_of_perm k j π⟩ : SimplexIndex d k) := by
  exact (simplexCell_eq_kuhn k
    (⟨(gridOffset k j, π), mem_triangulation_of_perm k j π⟩ : SimplexIndex d k)).symm

theorem integrableOn_triadicCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) {w : Vec d → ℝ}
    (hw : IntegrableOn w (originCube 1) volume) : IntegrableOn w (triadicCube k j) volume := by
  have h1 : IntegrableOn w (⋃ π : Equiv.Perm (Fin d),
      kuhnSimplex (-(k : ℤ)) π (triadicCentre k j)) volume := by
    apply integrableOn_finite_iUnion.mpr
    intro π
    rw [kuhn_eq_simplexCell]
    exact hw.mono_set (CoarseDeGiorgi.simplexCell_subset_originCube k _)
  rw [triadicCube_eq]
  exact h1.congr_set_ae (iUnion_kuhnSimplex_ae_eq_cube _ _).symm

/-- The `p`-th power mean over the triadic cubes of level `k`. -/
noncomputable def cubePowerMean {d : ℕ} (k : ℕ) (w : Vec d → ℝ) (p : ℝ) : ℝ :=
  (∑ j : Fin d → Fin (3 ^ k), Real.rpow (volumeAverage (triadicCube k j) w) p) /
    ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)

/-- Jensen: the power mean over cubes is at most the power mean over the simplices. -/
theorem cubePowerMean_le_simplex {d : ℕ} (k : ℕ) {w : Vec d → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hw : IntegrableOn w (originCube 1) volume) {p : ℝ} (hp : 1 ≤ p) :
    cubePowerMean k w p ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow (volumeAverage (simplexCell k η) w) p) /
          ((triangulation (d := d) k).card : ℝ) := by
  classical
  have hfac : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hnn : ∀ (V : Set (Vec d)), 0 ≤ volumeAverage V w := fun V => by
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hw0)
  -- Jensen on one cube
  have hcube : ∀ j : Fin d → Fin (3 ^ k),
      Real.rpow (volumeAverage (triadicCube k j) w) p ≤ (d.factorial : ℝ)⁻¹ *
        ∑ π : Equiv.Perm (Fin d),
          Real.rpow (volumeAverage (kuhnSimplex (-(k : ℤ)) π (triadicCentre k j)) w) p := by
    intro j
    rw [volumeAverage_triadicCube k j (integrableOn_triadicCube k j hw)]
    have hj := Real.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ)
      (w := fun _ : Equiv.Perm (Fin d) => (d.factorial : ℝ)⁻¹)
      (z := fun π => volumeAverage (kuhnSimplex (-(k : ℤ)) π (triadicCentre k j)) w)
      (fun _ _ => inv_nonneg.mpr hfac.le)
      (by simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hfac.ne'])
      (fun π _ => hnn _) hp
    simp only [Real.rpow_eq_pow, ← Finset.mul_sum] at hj ⊢
    exact hj
  -- reindex the simplex sum
  have hsum : ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow (volumeAverage (simplexCell k η) w) p) =
      ∑ j : Fin d → Fin (3 ^ k), ∑ π : Equiv.Perm (Fin d),
        Real.rpow (volumeAverage (kuhnSimplex (-(k : ℤ)) π (triadicCentre k j)) w) p := by
    let G : (Fin d → ℤ) × Equiv.Perm (Fin d) → ℝ := fun x =>
      Real.rpow (volumeAverage (simplex (-(k : ℤ)) x.2
        (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (x.1 i : ℝ))) w) p
    have h1 : ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow (volumeAverage (simplexCell k η) w) p) =
        ∑ x ∈ triangulation (d := d) k, G x :=
      Finset.sum_attach (triangulation (d := d) k) G
    rw [h1]
    unfold triangulation
    rw [Finset.sum_image]
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro π _
      change Real.rpow (volumeAverage (simplex (-(k : ℤ)) π
        (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ))) w) p = _
      rw [CoarseDeGiorgi.Moments.simplex_eq_kuhnSimplex]
      rfl
    · intro x _ y _ hxy
      have h1 : gridOffset k x.1 = gridOffset k y.1 := congrArg Prod.fst hxy
      exact Prod.ext (CoarseDeGiorgi.Moments.gridOffset_injective k h1)
        (congrArg (fun v : (Fin d → ℤ) × Equiv.Perm (Fin d) => v.2) hxy)
  have hcardT : ((triangulation (d := d) k).card : ℝ) =
      (d.factorial : ℝ) * (3 : ℝ) ^ (k * d) := by
    rw [CoarseDeGiorgi.Moments.triangulation_card]
    push_cast
    ring
  have hcardJ : ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ) = (3 : ℝ) ^ (k * d) := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [← pow_mul]
  unfold cubePowerMean
  rw [hsum, hcardT, hcardJ]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (k * d) := by positivity
  rw [div_le_div_iff₀ h3 (mul_pos hfac h3)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d → Fin (3 ^ k)))) => hcube j)
  rw [← Finset.mul_sum] at hs
  have hsn : 0 ≤ ∑ j : Fin d → Fin (3 ^ k), ∑ π : Equiv.Perm (Fin d),
      Real.rpow (volumeAverage (kuhnSimplex (-(k : ℤ)) π (triadicCentre k j)) w) p :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun π _ => Real.rpow_nonneg (hnn _) _
  calc _ ≤ ((d.factorial : ℝ)⁻¹ * ∑ j : Fin d → Fin (3 ^ k), ∑ π : Equiv.Perm (Fin d),
        Real.rpow (volumeAverage (kuhnSimplex (-(k : ℤ)) π (triadicCentre k j)) w) p) *
        ((d.factorial : ℝ) * (3 : ℝ) ^ (k * d)) :=
      mul_le_mul_of_nonneg_right hs (mul_pos hfac h3).le
    _ = _ := by field_simp

end CoarseDeGiorgi.SharpnessExamples
