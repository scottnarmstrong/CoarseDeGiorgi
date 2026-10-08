module

public import CoarseDeGiorgi.Cubical.MomentsSecond

/-! # The first inequality of Lemma `l.cubical.simplicial.moments`: cubes are controlled by simplices -/

@[expose] public section

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

theorem cubeCell_eq_simplexCube (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    cubeCell k j = Foundations.Simplex.simplexCube (-(k : ℤ))
      (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) := by
  ext x
  simp only [cubeCell, originCube, Foundations.Simplex.simplexCube, Set.mem_ofPred_eq, Pi.sub_apply]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The simplex of `𝒯_k` determined by a cube index and a permutation. -/
noncomputable def simplexIdx (k : ℕ) (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) :
    SimplexIndex d k :=
  ⟨(gridOffset k j, π), by
    classical
    exact Finset.mem_image.mpr ⟨(j, π), Finset.mem_univ _, rfl⟩⟩

theorem simplexCell_simplexIdx (k : ℕ) (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) :
    simplexCell k (simplexIdx k j π) = Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) :=
  Moments.simplex_eq_kuhnSimplex _ _ _

theorem volume_ratio_cube (k : ℕ) (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) :
    (volume (simplexCell k (simplexIdx k j π))).toReal / (volume (cubeCell k j)).toReal =
      ((Nat.factorial d : ℝ))⁻¹ := by
  rw [volume_simplexCell_toReal, volume_cubeCell_toReal]
  have hf : (0 : ℝ) < (Nat.factorial d : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have : ((3 : ℝ) ^ (k * d)) = ((3 : ℝ) ^ k) ^ d := by rw [pow_mul]
  rw [this, inv_pow, mul_inv]
  have h3 : ((3 : ℝ) ^ k) ^ d ≠ 0 := by positivity
  field_simp

theorem gridOffset_injective (k : ℕ) : Function.Injective (fun j : Fin d → Fin (3 ^ k) => gridOffset k j) := by
  intro j j' h
  funext i
  have := congrFun h i
  simp only [gridOffset] at this
  exact Fin.ext (by omega)

theorem sum_simplex_reindex (k : ℕ) (F : SimplexIndex d k → ℝ) :
    ∑ η ∈ (triangulation (d := d) k).attach, F η =
      ∑ j : Fin d → Fin (3 ^ k), ∑ π : Equiv.Perm (Fin d), F (simplexIdx k j π) := by
  classical
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun x _ => simplexIdx k x.1 x.2) (fun _ _ => Finset.mem_attach _ _) ?_ ?_ ?_
  · intro x _ y _ h
    have h1 : (gridOffset k x.1, x.2) = (gridOffset k y.1, y.2) := congrArg Subtype.val h
    have := Prod.mk.inj h1
    exact Prod.ext (gridOffset_injective k this.1) this.2
  · intro η _
    obtain ⟨jp, _, hjp⟩ := Finset.mem_image.mp η.2
    exact ⟨jp, Finset.mem_univ _, Subtype.ext hjp⟩
  · intro x _; rfl

/-- Cube responses are controlled by the simplices inside them. -/
theorem cube_le_simplices (D : RespData d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    ‖D.cube a ha k j‖ ≤ (Nat.factorial d : ℝ)⁻¹ *
      ∑ π : Equiv.Perm (Fin d), ‖D.simplex a ha k (simplexIdx k j π)‖ := by
  classical
  let V : Equiv.Perm (Fin d) → Set (Vec d) := fun π => simplexCell k (simplexIdx k j π)
  have hdisj : Pairwise (Function.onFun Disjoint V) := by
    intro π τ hne
    simp only [Function.onFun, V, simplexCell_simplexIdx]
    exact Foundations.Simplex.pairwise_disjoint_kuhnSimplex _ _ hne
  have hcover : volume (cubeCell k j \ ⋃ π, V π) = 0 := by
    have h := Foundations.Simplex.iUnion_kuhnSimplex_ae_eq_cube (-(k : ℤ))
      (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ))
    rw [← cubeCell_eq_simplexCube] at h
    have h2 : (⋃ π, V π) = ⋃ π, Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
        (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) := by
      simp only [V, simplexCell_simplexIdx]
    rw [h2]
    exact (ae_eq_set.mp h.symm).1
  have hVU : ∀ π, V π ⊆ cubeCell k j := fun π => by
    simp only [V, simplexCell_simplexIdx, cubeCell_eq_simplexCube]
    exact Foundations.Simplex.kuhnSimplex_subset_cube _ _ _
  obtain ⟨_, hle⟩ := D.norm_le_tsum a (cubeCell k j) (cubeCell_isOpenBoundedConvexDomain k j)
    (cubeCell_nonempty k j) (weightedCoeffOn_cubeCell k a ha j) V
    (fun π => simplexCell_isOpenBoundedConvexDomain k _) (fun π => simplexCell_nonempty k _)
    (fun π => weightedCoeffOn_simplexCell k a ha _) hVU hdisj hcover
  rw [tsum_fintype] at hle
  have : ∀ π, (volume (V π)).toReal / (volume (cubeCell k j)).toReal = (Nat.factorial d : ℝ)⁻¹ :=
    fun π => volume_ratio_cube k j π
  simp only [this, ← Finset.mul_sum] at hle
  exact hle

theorem first_avg (D : RespData d) (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {p : ℝ} (hp : 1 ≤ p) (k : ℕ) : D.cubeAvg a ha k p ≤ D.simplexAvg a ha k p := by
  classical
  have hp0 : 0 < p := by linarith
  have hf : (0 : ℝ) < (Nat.factorial d : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hM : ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ) = ((3 : ℝ) ^ k) ^ d := by
    simp [Finset.card_univ]
  have hMpos : (0 : ℝ) < ((3 : ℝ) ^ k) ^ d := by positivity
  have hcard : ((triangulation (d := d) k).card : ℝ) = (Nat.factorial d : ℝ) * ((3 : ℝ) ^ k) ^ d := by
    rw [triangulation_card]; push_cast; rw [pow_mul]
  have hj : ∀ j : Fin d → Fin (3 ^ k), Real.rpow ‖D.cube a ha k j‖ p ≤
      (Nat.factorial d : ℝ)⁻¹ * ∑ π : Equiv.Perm (Fin d),
        Real.rpow ‖D.simplex a ha k (simplexIdx k j π)‖ p := by
    intro j
    have h1 := Real.rpow_le_rpow (norm_nonneg _) (cube_le_simplices D a ha k j) hp0.le
    have h2 := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.univ : Finset (Equiv.Perm (Fin d)))
      (fun _ => (Nat.factorial d : ℝ)⁻¹) (fun π => ‖D.simplex a ha k (simplexIdx k j π)‖)
      (fun _ _ => by positivity)
      (by simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm]; field_simp) (fun _ _ => norm_nonneg _) hp
    rw [← Finset.mul_sum] at h2
    rw [← Finset.mul_sum] at h2
    exact h1.trans h2
  unfold RespData.cubeAvg RespData.simplexAvg
  rw [hM, hcard, sum_simplex_reindex k (fun η => Real.rpow ‖D.simplex a ha k η‖ p), div_le_div_iff₀ hMpos (by positivity)]
  calc (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖D.cube a ha k j‖ p) * ((Nat.factorial d : ℝ) * ((3 : ℝ) ^ k) ^ d)
      ≤ ((Nat.factorial d : ℝ)⁻¹ * ∑ j : Fin d → Fin (3 ^ k), ∑ π : Equiv.Perm (Fin d),
          Real.rpow ‖D.simplex a ha k (simplexIdx k j π)‖ p) * ((Nat.factorial d : ℝ) * ((3 : ℝ) ^ k) ^ d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => hj j
    _ = _ := by field_simp

end CoarseDeGiorgi.Cubical
