import CoarseDeGiorgi.NegSobolev.GaussianCells
import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
import CoarseDeGiorgi.CoefficientConditions.BesovGeom
import CoarseDeGiorgi.Statements.CubeCellIsOpenBoundedConvexDomain

/-! # Measure partitions for the two triadic families -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- Disjoint finite cells covering a carrier almost everywhere partition its restricted measure. -/
theorem restrict_eq_sum_of_partition {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (V : Set α) (U : ι → Set α) (hU : ∀ i, MeasurableSet (U i))
    (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hc : (⋃ i, U i) =ᵐ[μ] V) : μ.restrict V = ∑ i, μ.restrict (U i) := by
  classical
  rw [← Measure.restrict_congr_set hc, Measure.restrict_iUnion hd hU, Measure.sum_fintype]

/-- The simplices give a measure partition of the unit cube. -/
theorem simplexCell_measure_partition {d : ℕ} (k : ℕ) :
    volume.restrict (originCube (d := d) 1) = ∑ η : SimplexIndex d k,
      volume.restrict (simplexCell k η) :=
  restrict_eq_sum_of_partition volume _ _
    (fun η => (simplexCell_isOpenBoundedConvexDomain k η).isOpen.measurableSet)
    (Assembly.ClassicalMomentsImpl.simplexCell_pairwise_disjoint k)
    (Assembly.ClassicalMomentsImpl.simplexCell_union_ae k)

/-- Distinct triadic cubes are disjoint. -/
theorem cubeCell_pairwise_disjoint {d : ℕ} (k : ℕ) :
    Pairwise (fun j l : Fin d → Fin (3 ^ k) => Disjoint (cubeCell k j) (cubeCell k l)) := by
  intro j l hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hne
  funext i
  have hs : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hxi := hx i
  have hyi := hy i
  simp only [Pi.sub_apply, gridOffset, Int.cast_sub, Int.cast_natCast] at hxi hyi
  have h1 : ((j i).val : ℝ) - ((l i).val : ℝ) < 1 := by
    nlinarith only [hs, hxi.1, hyi.2]
  have h2 : ((l i).val : ℝ) - ((j i).val : ℝ) < 1 := by
    nlinarith only [hs, hyi.1, hxi.2]
  have h1' : ((j i).val : ℤ) - ((l i).val : ℤ) < 1 := by exact_mod_cast h1
  have h2' : ((l i).val : ℤ) - ((j i).val : ℤ) < 1 := by exact_mod_cast h2
  apply Fin.ext
  omega

/-- Every cube has volume equal to its side length raised to the dimension. -/
theorem cubeCell_volume_side {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    (volume (cubeCell k j)).toReal = ((3 : ℝ) ^ (-(k : ℤ))) ^ d := by
  change (volume (CoefficientConditions.cubeSet k j)).toReal = _
  rw [CoefficientConditions.cubeSet_eq, Foundations.Simplex.volume_simplexCube,
    ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le, zpow_mul, zpow_natCast]

/-- A simplex has `1/d!` of the volume of a cube with the same side length. -/
theorem simplexCell_volume_side {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    (volume (simplexCell k η)).toReal = ((3 : ℝ) ^ (-(k : ℤ))) ^ d / (d.factorial : ℝ) := by
  change (volume (simplex (-(k : ℤ)) η.val.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ)))).toReal = _
  rw [Moments.simplex_eq_kuhnSimplex, Foundations.Simplex.volume_kuhnSimplex,
    ENNReal.toReal_div, ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le,
    zpow_mul, zpow_natCast, ENNReal.toReal_natCast]

/-- Equal volumes are reciprocal to the number of triadic cubes. -/
theorem cubeCell_volume_real {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    (volume (cubeCell k j)).toReal =
      ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)⁻¹ := by
  rw [cubeCell_volume_side]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    zpow_neg, zpow_natCast, inv_pow]

/-- The cubes cover the unit cube up to a null set. -/
theorem cubeCell_union_ae {d : ℕ} (k : ℕ) :
    (⋃ j : Fin d → Fin (3 ^ k), cubeCell k j) =ᵐ[volume] originCube 1 := by
  classical
  let V := ⋃ j : Fin d → Fin (3 ^ k), cubeCell k j
  have hsub : V ⊆ originCube 1 := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact CoefficientConditions.cubeSet_subset_originCube k j hj
  have hm (j : Fin d → Fin (3 ^ k)) : MeasurableSet (cubeCell k j) :=
    (cubeCell_isOpenBoundedConvexDomain k j).isOpen.measurableSet
  have hfin : volume V ≠ ⊤ := ne_top_of_le_ne_top
    (by simp [Assembly.ClassicalMomentsImpl.originCube_volume_one]) (measure_mono hsub)
  have hcfin (j : Fin d → Fin (3 ^ k)) : volume (cubeCell k j) ≠ ⊤ :=
    (cubeCell_isOpenBoundedConvexDomain k j).isBoundedDomain.isBounded.measure_lt_top.ne
  have hN : (0 : ℝ) < ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    positivity
  have hreal : (volume V).toReal = 1 := by
    rw [show V = ⋃ j : Fin d → Fin (3 ^ k), cubeCell k j from rfl,
      measure_iUnion (cubeCell_pairwise_disjoint k) hm, tsum_fintype,
      ENNReal.toReal_sum (fun j _ => hcfin j)]
    simp only [cubeCell_volume_real, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have hv : volume V = 1 := by
    rw [← ENNReal.ofReal_toReal hfin, hreal, ENNReal.ofReal_one]
  apply ae_eq_of_subset_of_measure_ge hsub
  · rw [hv, Assembly.ClassicalMomentsImpl.originCube_volume_one]
  · exact (MeasurableSet.iUnion hm).nullMeasurableSet
  · simp [Assembly.ClassicalMomentsImpl.originCube_volume_one]

/-- The cubes give a measure partition of the unit cube. -/
theorem cubeCell_measure_partition {d : ℕ} (k : ℕ) :
    volume.restrict (originCube (d := d) 1) = ∑ j : Fin d → Fin (3 ^ k),
      volume.restrict (cubeCell k j) :=
  restrict_eq_sum_of_partition volume _ _
    (fun j => (cubeCell_isOpenBoundedConvexDomain k j).isOpen.measurableSet)
    (cubeCell_pairwise_disjoint k) (cubeCell_union_ae k)

end CoarseDeGiorgi.NegSobolev
