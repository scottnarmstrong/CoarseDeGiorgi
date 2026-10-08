module

public import CoarseDeGiorgi.Whitney.SeedResidual
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Refinement of the triadic nodal partition

Splitting a common rounding threshold into its three triadic subintervals
couples a fine vertex with a coarse vertex. This realizes fine interpolation
without choosing a cell on a face.
-/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- Coarse vertex obtained from a fine vertex and one common rounding bin. -/
def seedParent (a : Fin 3) (m : Fin d → ℤ) : Fin d → ℤ :=
  fun i => (m i + (a.val : ℤ) - 1) / 3

theorem rounding_parent_floor (k : ℕ) (a : Fin 3) (x t : ℝ) :
    ⌊x / seedScale k - 1 / 2 + t⌋ =
      (⌊x / seedScale (k + 1) - 1 / 2 + (3 * t - a.val)⌋ + (a.val : ℤ) - 1) / 3 := by
  have hs := three_mul_seedScale_succ k
  have hp := seedScale_pos (k + 1)
  have hratio : x / seedScale (k + 1) = 3 * (x / seedScale k) := by
    rw [← hs]
    field_simp
  have heq : (x / seedScale k - 1 / 2 + t) * 3 =
      (x / seedScale (k + 1) - 1 / 2 + (3 * t - a.val)) +
        (((a.val : ℤ) - 1 : ℤ) : ℝ) := by
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    linarith only [hratio]
  calc
    ⌊x / seedScale k - 1 / 2 + t⌋ =
        ⌊(x / seedScale k - 1 / 2 + t) * (3 : ℕ)⌋ / 3 :=
      (Int.mul_natCast_floor_div_cancel (by norm_num : (3 : ℕ) ≠ 0) _).symm
    _ = _ := by
      norm_num only [Nat.cast_ofNat]
      rw [heq, Int.floor_add_intCast]
      omega

private theorem bin_floor {a : Fin 3} {t : ℝ}
    (ht : 3 * t - a.val ∈ Ico 0 1) : ⌊3 * t⌋ = (a.val : ℤ) := by
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_natCast]
  constructor <;> linarith only [ht.1, ht.2]

private theorem in_unit_of_bin {a : Fin 3} {t : ℝ}
    (ht : 3 * t - a.val ∈ Ico 0 1) : t ∈ Ico 0 1 := by
  have ha0 : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
  have ha2 : (a.val : ℝ) ≤ 2 := by exact_mod_cast (show a.val ≤ 2 by omega)
  constructor <;> linarith only [ht.1, ht.2, ha0, ha2]

/-- One piece of a coarse rounding cell, indexed by a fine vertex and a bin. -/
def seedRefinementCell (k : ℕ) (M : Fin d → ℤ) (x : Vec d)
    (p : Fin 3 × (Fin d → ℤ)) : Set ℝ :=
  {t | seedParent p.1 p.2 = M ∧
    3 * t - p.1.val ∈ nodalRoundingCell (k + 1) p.2 x}

theorem iUnion_seedRefinementCell (k : ℕ) (M : Fin d → ℤ) (x : Vec d) :
    (⋃ p : Fin 3 × (Fin d → ℤ), seedRefinementCell k M x p) =
      nodalRoundingCell k M x := by
  ext t
  constructor
  · intro ht
    obtain ⟨⟨a, m⟩, hparent, hfine⟩ := mem_iUnion.mp ht
    refine ⟨in_unit_of_bin hfine.1, fun i => ?_⟩
    apply Int.floor_eq_iff.mp
    rw [rounding_parent_floor k a (x i) t, Int.floor_eq_iff.mpr (hfine.2 i)]
    exact congrFun hparent i
  · intro ht
    have hb0 : (0 : ℤ) ≤ ⌊3 * t⌋ := Int.floor_nonneg.mpr (by linarith only [ht.1.1])
    have hb3 : ⌊3 * t⌋ < (3 : ℤ) := Int.floor_lt.mpr (by
      norm_num only [Int.cast_ofNat]
      linarith only [ht.1.2])
    let a : Fin 3 := ⟨⌊3 * t⌋.toNat, by omega⟩
    have hai : (a.val : ℤ) = ⌊3 * t⌋ := by
      simp only [a, Int.toNat_of_nonneg hb0]
    have har : (a.val : ℝ) = (⌊3 * t⌋ : ℝ) := by exact_mod_cast hai
    have hf0 : 0 ≤ 3 * t - a.val := by
      rw [har]
      exact sub_nonneg.mpr (Int.floor_le _)
    have hf1 : 3 * t - a.val < 1 := by
      rw [har]
      linarith only [Int.lt_floor_add_one (3 * t)]
    let m : Fin d → ℤ := fun i => ⌊x i / seedScale (k + 1) - 1 / 2 + (3 * t - a.val)⌋
    apply mem_iUnion.mpr
    refine ⟨(a, m), ?_, ⟨hf0, hf1⟩, fun i => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩⟩
    funext i
    have hc := Int.floor_eq_iff.mpr (ht.2 i)
    rw [rounding_parent_floor k a (x i) t] at hc
    exact hc

theorem pairwise_disjoint_seedRefinementCell (k : ℕ) (M : Fin d → ℤ) (x : Vec d) :
    Pairwise (fun p q : Fin 3 × (Fin d → ℤ) =>
      Disjoint (seedRefinementCell k M x p) (seedRefinementCell k M x q)) := by
  rintro ⟨a, m⟩ ⟨b, n⟩ hne
  apply Set.disjoint_left.mpr
  intro t hm hn
  have ha := bin_floor hm.2.1
  have hb := bin_floor hn.2.1
  have hab : a = b := by
    apply Fin.ext
    exact_mod_cast ha.symm.trans hb
  subst b
  have hmn : m = n := by
    funext i
    exact (Int.floor_eq_iff.mpr (hm.2.2 i)).symm.trans
      (Int.floor_eq_iff.mpr (hn.2.2 i))
  exact hne (by rw [hmn])

/-- Left endpoint of a transformed fine rounding interval. -/
def seedRefinementLower (k : ℕ) (a : Fin 3) (m : Fin d → ℤ) (x : Vec d) : ℝ :=
  (positivePeak (seedNode (k + 1) m - x) / seedScale (k + 1) + a.val) / 3

/-- Right endpoint of a transformed fine rounding interval. -/
def seedRefinementUpper (k : ℕ) (a : Fin 3) (m : Fin d → ℤ) (x : Vec d) : ℝ :=
  (1 - positivePeak (x - seedNode (k + 1) m) / seedScale (k + 1) + a.val) / 3

theorem seedRefinementCell_eq_interval (k : ℕ) (M m : Fin d → ℤ) (a : Fin 3)
    (x : Vec d) : seedRefinementCell k M x (a, m) =
      if seedParent a m = M then
        Ico (seedRefinementLower k a m x) (seedRefinementUpper k a m x) else ∅ := by
  classical
  by_cases h : seedParent a m = M
  · rw [ite_eq_left h]
    ext t
    simp only [seedRefinementCell, h, true_and, nodalRoundingCell_eq_Ico,
      Set.mem_ofPred_eq, Set.mem_Ico, seedRefinementLower, seedRefinementUpper]
    constructor
    · rintro ⟨hl, hu⟩
      constructor
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
        linarith only [hl]
      · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
        linarith only [hu]
    · rintro ⟨hl, hu⟩
      have hl' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mp hl
      have hu' := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mp hu
      constructor <;> linarith only [hl', hu']
  · rw [ite_eq_right h]
    ext t
    simp only [seedRefinementCell, h, false_and, Set.mem_ofPred_eq, Set.mem_empty_iff_false]

theorem measurableSet_seedRefinementCell (k : ℕ) (M : Fin d → ℤ) (x : Vec d)
    (p : Fin 3 × (Fin d → ℤ)) : MeasurableSet (seedRefinementCell k M x p) := by
  rw [seedRefinementCell_eq_interval]
  split_ifs
  · exact measurableSet_Ico
  · exact MeasurableSet.empty

theorem seedRefinementCell_volume_ne_top (k : ℕ) (M : Fin d → ℤ) (x : Vec d)
    (p : Fin 3 × (Fin d → ℤ)) : volume (seedRefinementCell k M x p) ≠ ⊤ := by
  rw [seedRefinementCell_eq_interval]
  split_ifs
  · rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  · rw [measure_empty]
    exact ENNReal.zero_ne_top

theorem seedRefinementCell_volume_toReal (k : ℕ) (M : Fin d → ℤ) (x : Vec d)
    (p : Fin 3 × (Fin d → ℤ)) : (volume (seedRefinementCell k M x p)).toReal =
      if seedParent p.1 p.2 = M then seedHat (k + 1) p.2 x / 3 else 0 := by
  classical
  rw [seedRefinementCell_eq_interval]
  by_cases h : seedParent p.1 p.2 = M
  · rw [ite_eq_left h, ite_eq_left h, Real.volume_Ico, ENNReal.toReal_ofReal']
    have heq : seedRefinementUpper k p.1 p.2 x - seedRefinementLower k p.1 p.2 x =
        (1 - (positivePeak (x - seedNode (k + 1) p.2) +
          positivePeak (seedNode (k + 1) p.2 - x)) / seedScale (k + 1)) / 3 := by
      unfold seedRefinementUpper seedRefinementLower
      ring
    rw [heq]
    unfold seedHat nodalHat
    let v := 1 - (positivePeak (x - seedNode (k + 1) p.2) +
      positivePeak (seedNode (k + 1) p.2 - x)) / seedScale (k + 1)
    change max (v / 3) 0 = max 0 v / 3
    by_cases hv : 0 ≤ v
    · rw [max_eq_left (div_nonneg hv (by norm_num)), max_eq_right hv]
    · have hv' := (lt_of_not_ge hv).le
      rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hv' (by norm_num)),
        max_eq_left hv', zero_div]
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [measure_empty, ENNReal.toReal_zero]

/-- Exact three-bin refinement kernel for a coarse hat. -/
theorem seedHat_refinement_kernel (k : ℕ) (M : Fin d → ℤ) (x : Vec d) :
    seedHat k M x = ∑' p : Fin 3 × (Fin d → ℤ),
      if seedParent p.1 p.2 = M then seedHat (k + 1) p.2 x / 3 else 0 := by
  classical
  calc
    seedHat k M x = (volume (nodalRoundingCell k M x)).toReal :=
      seedHat_eq_rounding_volume k M x
    _ = (∑' p : Fin 3 × (Fin d → ℤ), volume (seedRefinementCell k M x p)).toReal := by
      rw [← iUnion_seedRefinementCell, measure_iUnion
        (pairwise_disjoint_seedRefinementCell k M x)
        (fun p => measurableSet_seedRefinementCell k M x p)]
    _ = ∑' p : Fin 3 × (Fin d → ℤ), (volume (seedRefinementCell k M x p)).toReal :=
      ENNReal.tsum_toReal_eq (seedRefinementCell_volume_ne_top k M x)
    _ = _ := tsum_congr fun p => seedRefinementCell_volume_toReal k M x p

private theorem summable_refinement_kernel (k : ℕ) (M : Fin d → ℤ) (x : Vec d) :
    Summable (fun p : Fin 3 × (Fin d → ℤ) =>
      if seedParent p.1 p.2 = M then seedHat (k + 1) p.2 x / 3 else 0) := by
  classical
  apply summable_of_hasFiniteSupport
  apply (Set.finite_univ.prod (finite_seedHat_support (k + 1) x)).subset
  intro p hp
  refine ⟨Set.mem_univ _, ?_⟩
  by_contra hh
  have hz : seedHat (k + 1) p.2 x = 0 := by
    simpa only [Function.mem_support, not_not] using hh
  apply hp
  simp only [hz, zero_div, ite_self]

theorem seedHat_at_fine_node (k : ℕ) (M m : Fin d → ℤ) :
    seedHat k M (seedNode (k + 1) m) =
      ∑ a : Fin 3, if seedParent a m = M then (1 : ℝ) / 3 else 0 := by
  classical
  rw [seedHat_refinement_kernel,
    (summable_refinement_kernel k M (seedNode (k + 1) m)).tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [tsum_eq_single m]
  · simp only [seedHat_at_node, ite_true]
  · intro n hnm
    rw [seedHat_at_node, ite_eq_right hnm, zero_div, ite_self]

/-- Every coarse hat is the fine interpolant of its nodal values. -/
theorem seedHat_refinement (k : ℕ) (M : Fin d → ℤ) (x : Vec d) :
    seedHat k M x = ∑' m : Fin d → ℤ,
      seedHat k M (seedNode (k + 1) m) * seedHat (k + 1) m x := by
  classical
  have ha (a : Fin 3) : Summable (fun m : Fin d → ℤ =>
      if seedParent a m = M then seedHat (k + 1) m x / 3 else 0) := by
    apply summable_of_hasFiniteSupport
    apply (finite_seedHat_support (k + 1) x).subset
    intro m hm
    by_contra hh
    have hz : seedHat (k + 1) m x = 0 := by
      simpa only [Function.mem_support, not_not] using hh
    apply hm
    simp only [hz, zero_div, ite_self]
  calc
    seedHat k M x = ∑ a : Fin 3, ∑' m : Fin d → ℤ,
        if seedParent a m = M then seedHat (k + 1) m x / 3 else 0 := by
      rw [seedHat_refinement_kernel, (summable_refinement_kernel k M x).tsum_prod,
        tsum_fintype]
    _ = ∑' m : Fin d → ℤ, ∑ a : Fin 3,
        if seedParent a m = M then seedHat (k + 1) m x / 3 else 0 :=
      (Summable.tsum_finsetSum (fun a _ => ha a)).symm
    _ = _ := by
      apply tsum_congr
      intro m
      rw [seedHat_at_fine_node, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : seedParent a m = M
      · rw [ite_eq_left h, ite_eq_left h]
        ring
      · rw [ite_eq_right h, ite_eq_right h, zero_mul]

end

end CoarseDeGiorgi.Whitney

