import CoarseDeGiorgi.Cubical.SimplexBound
import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
import CoarseDeGiorgi.Statements.TriangulationCard

/-! # Counting and volumes for the Whitney layers of the simplices of `𝒯_k` -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

theorem volume_cubeCell_toReal (j : ℕ) (z : Fin d → Fin (3 ^ j)) :
    (volume (cubeCell j z)).toReal = (((3 : ℝ) ^ j)⁻¹) ^ d := by
  rw [cubeCell_eq_box, volume_box_toReal]

theorem volume_simplexCell_toReal (k : ℕ) (η : SimplexIndex d k) :
    (volume (simplexCell k η)).toReal = ((Nat.factorial d : ℝ) * (3 : ℝ) ^ (k * d))⁻¹ := by
  rw [Assembly.ClassicalMomentsImpl.simplexCell_volume_real, triangulation_card]
  push_cast; rfl

/-- The ratio of volumes of a cube of `𝒬_{k+l}` to a simplex of `𝒯_k` is the constant `d! 3^{-ld}`. -/
theorem volume_ratio (k l : ℕ) (η : SimplexIndex d k) (z : Fin d → Fin (3 ^ (k + l))) :
    (volume (cubeCell (k + l) z)).toReal / (volume (simplexCell k η)).toReal =
      (Nat.factorial d : ℝ) * (((3 : ℝ) ^ l)⁻¹) ^ d := by
  rw [volume_cubeCell_toReal, volume_simplexCell_toReal]
  have h1 : ((3 : ℝ) ^ (k + l))⁻¹ ^ d * ((Nat.factorial d : ℝ) * (3 : ℝ) ^ (k * d)) =
      (Nat.factorial d : ℝ) * (((3 : ℝ) ^ l)⁻¹) ^ d := by
    rw [pow_add, mul_inv, mul_pow, inv_pow, inv_pow]
    have : ((3 : ℝ) ^ (k * d)) = ((3 : ℝ) ^ k) ^ d := by rw [pow_mul]
    rw [this]
    have hk : ((3 : ℝ) ^ k) ^ d ≠ 0 := by positivity
    field_simp
  rw [div_eq_mul_inv, inv_inv]
  exact h1

/-- A cube of `𝒬_{k+l}` is a maximal cube for at most one simplex of `𝒯_k`. -/
theorem Wl_unique (k l : ℕ) {η η' : SimplexIndex d k} {z : Fin d → Fin (3 ^ (k + l))}
    (h : z ∈ Wl (simplexCell k η) k l) (h' : z ∈ Wl (simplexCell k η') k l) : η = η' := by
  by_contra hne
  have hdis := Assembly.ClassicalMomentsImpl.simplexCell_pairwise_disjoint k hne
  obtain ⟨x, hx⟩ := box_nonempty (k + l) (fun i => (z i : ℕ))
  exact Set.disjoint_left.mp hdis (box_subset_of_mem_Wl h hx) (box_subset_of_mem_Wl h' hx)

theorem sum_Wl_le (k l : ℕ) (f : (Fin d → Fin (3 ^ (k + l))) → ℝ≥0∞) :
    ∑ η ∈ (triangulation (d := d) k).attach, ∑ z ∈ Wl (simplexCell k η) k l, f z ≤
      ∑ z, f z := by
  classical
  calc ∑ η ∈ (triangulation (d := d) k).attach, ∑ z ∈ Wl (simplexCell k η) k l, f z
      = ∑ η ∈ (triangulation (d := d) k).attach, ∑ z, if z ∈ Wl (simplexCell k η) k l then f z else 0 := by
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [← Finset.sum_filter]; congr 1; ext z; simp
    _ = ∑ z, ∑ η ∈ (triangulation (d := d) k).attach, if z ∈ Wl (simplexCell k η) k l then f z else 0 :=
        Finset.sum_comm
    _ ≤ ∑ z, f z := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [← Finset.sum_filter]
        have hc : ((triangulation (d := d) k).attach.filter
            (fun η => z ∈ Wl (simplexCell k η) k l)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro η hη η' hη'
          exact Wl_unique k l (Finset.mem_filter.mp hη).2 (Finset.mem_filter.mp hη').2
        rw [Finset.sum_const, nsmul_eq_mul]
        calc _ ≤ ((1 : ℕ) : ℝ≥0∞) * f z := by
              apply mul_le_mul' _ le_rfl; exact_mod_cast hc
          _ = f z := by simp

/-- The layer volume bound for a simplex of `𝒯_k`. -/
theorem simplex_layer_weight (hd : 1 ≤ d) (k l : ℕ) (η : SimplexIndex d k) :
    ∑ z ∈ Wl (simplexCell k η) k l, (volume (cubeCell (k + l) z)).toReal ≤
      (10 * d * (d + 1) * ((3 : ℝ) ^ l)⁻¹) * (volume (simplexCell k η)).toReal := by
  obtain ⟨c₀, hc₀⟩ := kuhn_ball (d := d) (-(k : ℤ)) η.1.2 (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.1.1 i : ℝ))
  have hsimp : simplexCell k η = Foundations.Simplex.kuhnSimplex (-(k : ℤ)) η.1.2
      (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.1.1 i : ℝ)) := Moments.simplex_eq_kuhnSimplex _ _ _
  have hu : (3 : ℝ) ^ (-(k : ℤ)) = ((3 : ℝ) ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have := layer_weight (simplexCell_isOpenBoundedConvexDomain k η) hd k c₀
    (fun y hy => by rw [hsimp]; exact hc₀ y (by rwa [hu])) l
  simpa only [cubeCell_eq_box, volume_box_toReal] using this

end CoarseDeGiorgi.Cubical
