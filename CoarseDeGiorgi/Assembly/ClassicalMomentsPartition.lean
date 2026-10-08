import CoarseDeGiorgi.Assembly.ClassicalMomentsDefs
import CoarseDeGiorgi.Foundations.Simplex.Partition
import CoarseDeGiorgi.Moments.Cells

namespace CoarseDeGiorgi.Assembly.ClassicalMomentsImpl

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

theorem originCube_volume_one (d : ℕ) : volume (originCube (d := d) 1) = 1 := by
  have he : originCube (d := d) 1 = Foundations.Simplex.simplexCube 0 0 := by
    ext x
    simp [CoarseDeGiorgi.originCube, Foundations.Simplex.simplexCube, neg_div]
  rw [he, Foundations.Simplex.volume_simplexCube]
  simp

theorem simplexCell_pairwise_disjoint {d : ℕ} (k : ℕ) :
    Pairwise (fun η τ : SimplexIndex d k => Disjoint (simplexCell k η) (simplexCell k τ)) := by
  intro η τ hne
  apply disjoint_left.mpr
  intro x hx hy
  change x ∈ CoarseDeGiorgi.simplex (-(k : ℤ)) η.val.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ)) at hx
  change x ∈ CoarseDeGiorgi.simplex (-(k : ℤ)) τ.val.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (τ.val.1 i : ℝ)) at hy
  rw [Moments.simplex_eq_kuhnSimplex] at hx hy
  have hs : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hz : η.val.1 = τ.val.1 := by
    funext i
    have hl := (hx.1 i).1
    have hu := (hx.1 i).2
    have htl := (hy.1 i).1
    have htu := (hy.1 i).2
    change -(3 : ℝ) ^ (-(k : ℤ)) / 2 < x i -
      (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ) at hl
    change x i - (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ) <
      (3 : ℝ) ^ (-(k : ℤ)) / 2 at hu
    change -(3 : ℝ) ^ (-(k : ℤ)) / 2 < x i -
      (3 : ℝ) ^ (-(k : ℤ)) * (τ.val.1 i : ℝ) at htl
    change x i - (3 : ℝ) ^ (-(k : ℤ)) * (τ.val.1 i : ℝ) <
      (3 : ℝ) ^ (-(k : ℤ)) / 2 at htu
    have h1 : (η.val.1 i : ℝ) - (τ.val.1 i : ℝ) < 1 := by
      nlinarith only [hs, hl, htu]
    have h2 : (τ.val.1 i : ℝ) - (η.val.1 i : ℝ) < 1 := by
      nlinarith only [hs, htl, hu]
    have hi1 : η.val.1 i - τ.val.1 i < 1 := by exact_mod_cast h1
    have hi2 : τ.val.1 i - η.val.1 i < 1 := by exact_mod_cast h2
    omega
  have hp : η.val.2 ≠ τ.val.2 := by
    intro hp
    exact hne (Subtype.ext (Prod.ext hz hp))
  have hdis := Foundations.Simplex.pairwise_disjoint_kuhnSimplex
    (-(k : ℤ)) (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ)) hp
  apply disjoint_left.mp hdis hx
  simpa only [hz] using hy

theorem triangulation_card_pos (d k : ℕ) : 0 < (triangulation (d := d) k).card := by
  rw [triangulation_card]
  exact Nat.mul_pos (Nat.factorial_pos d) (pow_pos (by decide) _)

/-- Every cell has reciprocal-cardinality volume, including in dimension zero. -/
theorem simplexCell_volume_real {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    (volume (simplexCell k η)).toReal = ((triangulation (d := d) k).card : ℝ)⁻¹ := by
  change (volume (CoarseDeGiorgi.simplex (-(k : ℤ)) η.val.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ)))).toReal = _
  rw [Moments.simplex_eq_kuhnSimplex,
    Foundations.Simplex.volume_kuhnSimplex, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le]
  rw [triangulation_card]
  simp only [ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    neg_mul, zpow_neg]
  rw [← Nat.cast_mul, zpow_natCast]
  simp only [mul_inv_rev, div_eq_mul_inv]

theorem simplexCell_union_ae {d : ℕ} (k : ℕ) :
    (⋃ η : SimplexIndex d k, simplexCell k η) =ᵐ[volume] originCube 1 := by
  classical
  let U := ⋃ η : SimplexIndex d k, simplexCell k η
  have hsub : U ⊆ originCube 1 := by
    intro x hx
    obtain ⟨η, hη⟩ := mem_iUnion.mp hx
    exact CoarseDeGiorgi.simplexCell_subset_originCube k η hη
  have hm (η : SimplexIndex d k) : MeasurableSet (simplexCell k η) :=
    (simplexCell_isOpenBoundedConvexDomain k η).isOpen.measurableSet
  have hfin : volume U ≠ ⊤ := ne_top_of_le_ne_top (by simp [originCube_volume_one])
    (measure_mono hsub)
  have hcfin (η : SimplexIndex d k) : volume (simplexCell k η) ≠ ⊤ :=
    (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
  have hN : ((triangulation (d := d) k).card : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (triangulation_card_pos d k)).ne'
  have hreal : (volume U).toReal = 1 := by
    rw [show U = ⋃ η : SimplexIndex d k, simplexCell k η from rfl,
      measure_iUnion (simplexCell_pairwise_disjoint k) hm, tsum_fintype,
      ENNReal.toReal_sum (fun η _ => hcfin η)]
    simp only [simplexCell_volume_real, Finset.sum_const, Finset.card_univ,
      CoarseDeGiorgi.SimplexIndex, Fintype.card_coe, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN
  have hv : volume U = 1 := by
    rw [← ENNReal.ofReal_toReal hfin, hreal]
    norm_num
  apply ae_eq_of_subset_of_measure_ge hsub
  · rw [hv, originCube_volume_one]
  · exact (MeasurableSet.iUnion hm).nullMeasurableSet
  · simp [originCube_volume_one]

/-- The display `e.partition.average` for the triadic triangulation. -/
theorem partition_average {d : ℕ} (k : ℕ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (originCube 1)) :
    ((triangulation (d := d) k).attach.sum fun η => volumeAverage (simplexCell k η) f) /
      ((triangulation (d := d) k).card : ℝ) = ∫ x in originCube 1, f x := by
  classical
  let RawIndex := {i : (Fin d → ℤ) × Equiv.Perm (Fin d) // i ∈ triangulation k}
  change ((triangulation (d := d) k).attach.sum
      fun η : RawIndex => volumeAverage
        (simplexCell k (show SimplexIndex d k from η)) f) /
      ((triangulation (d := d) k).card : ℝ) = ∫ x in originCube 1, f x
  have hN : ((triangulation (d := d) k).card : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (triangulation_card_pos d k)).ne'
  have hdis : Pairwise (fun η τ : RawIndex =>
      Disjoint (simplexCell k (show SimplexIndex d k from η))
        (simplexCell k (show SimplexIndex d k from τ))) := by
    intro η τ hne
    apply simplexCell_pairwise_disjoint k
    intro heq
    exact hne heq
  have hi := integral_iUnion_fintype
    (fun η : RawIndex =>
      (simplexCell_isOpenBoundedConvexDomain k
        (show SimplexIndex d k from η)).isOpen.measurableSet)
    hdis
    (fun η => hf.mono_set (CoarseDeGiorgi.simplexCell_subset_originCube k
      (show SimplexIndex d k from η)))
  have hSet : (⋃ η : RawIndex,
      simplexCell k (show SimplexIndex d k from η)) =
        ⋃ η : SimplexIndex d k, simplexCell k η := by rfl
  have hUnion : (⋃ η : RawIndex,
      simplexCell k (show SimplexIndex d k from η)) =ᵐ[volume] originCube 1 :=
    hSet ▸ simplexCell_union_ae (d := d) k
  rw [setIntegral_congr_set hUnion] at hi
  change (∫ x in originCube 1, f x) =
      ∑ i : RawIndex, ∫ x in simplexCell k (show SimplexIndex d k from i), f x at hi
  rw [← Finset.sum_coe_sort_eq_attach]
  change (∑ i : RawIndex,
      (volume (simplexCell k (show SimplexIndex d k from i))).toReal⁻¹ *
        ∫ x in simplexCell k (show SimplexIndex d k from i), f x) /
        ((triangulation (d := d) k).card : ℝ) = ∫ x in originCube 1, f x
  have hvol (i : RawIndex) :
      (volume (simplexCell k (show SimplexIndex d k from i))).toReal =
        ((triangulation (d := d) k).card : ℝ)⁻¹ :=
    simplexCell_volume_real k (show SimplexIndex d k from i)
  simp_rw [hvol, inv_inv]
  rw [← Finset.mul_sum (Finset.univ : Finset RawIndex) _ _,
    mul_div_cancel_left₀ _ hN, hi]


end CoarseDeGiorgi.Assembly.ClassicalMomentsImpl
