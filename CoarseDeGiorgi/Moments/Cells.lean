import CoarseDeGiorgi.Foundations.Simplex.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.SimplexIndex
import CoarseDeGiorgi.Statements.GridOffset
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.Simplex
import CoarseDeGiorgi.Statements.SimplexCell
import CoarseDeGiorgi.Statements.Triangulation
import Homogenization.Ambient.CoefficientField
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Ring.Parity
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Audited simplex cells for response moments

The public cell names alias the `Statements/` definitions. The geometric bridge
identifies the normalized-coordinate simplex `simplexCell` with the Kuhn API.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Moments

abbrev gridOffset {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Fin d → ℤ :=
  CoarseDeGiorgi.gridOffset k j

noncomputable abbrev triangulation {d : ℕ} (k : ℕ) :
    Finset ((Fin d → ℤ) × Equiv.Perm (Fin d)) := CoarseDeGiorgi.triangulation k

abbrev originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) := CoarseDeGiorgi.originCube ρ

noncomputable abbrev SimplexIndex (d k : ℕ) := CoarseDeGiorgi.SimplexIndex d k

abbrev simplexCell {d : ℕ} (k : ℕ) (η : SimplexIndex d k) : Set (Vec d) :=
  CoarseDeGiorgi.simplexCell k η

noncomputable instance {d k : ℕ} : Fintype (CoarseDeGiorgi.SimplexIndex d k) := by
  classical
  unfold CoarseDeGiorgi.SimplexIndex
  infer_instance

noncomputable instance {d k : ℕ} : Countable (CoarseDeGiorgi.SimplexIndex d k) := by
  classical
  unfold CoarseDeGiorgi.SimplexIndex
  infer_instance

/-- Compatibility name for the coefficient hypotheses `IsWeightedCoeffOn` on a cell. -/
abbrev IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  CoarseDeGiorgi.IsWeightedCoeffOn V a

/-- The normalized-coordinate simplex equals the coordinate-difference Kuhn simplex. -/
theorem simplex_eq_kuhnSimplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d))
    (z : Vec d) : CoarseDeGiorgi.simplex n π z = Foundations.Simplex.kuhnSimplex n π z := by
  unfold CoarseDeGiorgi.simplex
  have hs : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  ext x
  constructor
  · rintro ⟨y, rfl, hy, hord⟩
    constructor
    · intro i
      change -(3 : ℝ) ^ n / 2 < z i + (3 : ℝ) ^ n * y i - z i ∧
        z i + (3 : ℝ) ^ n * y i - z i < (3 : ℝ) ^ n / 2
      have hlo := mul_lt_mul_of_pos_left (hy i).1 hs
      have hhi := mul_lt_mul_of_pos_left (hy i).2 hs
      constructor <;> nlinarith only [hlo, hhi]
    · intro i j hij
      change z (π i) + (3 : ℝ) ^ n * y (π i) - z (π i) <
        z (π j) + (3 : ℝ) ^ n * y (π j) - z (π j)
      simpa only [add_sub_cancel_left] using mul_lt_mul_of_pos_left (hord i j hij) hs
  · intro hx
    refine ⟨fun i => (x i - z i) / (3 : ℝ) ^ n, ?_, ?_, ?_⟩
    · funext i
      change x i = z i + (3 : ℝ) ^ n * ((x i - z i) / (3 : ℝ) ^ n)
      rw [mul_div_cancel₀ _ hs.ne']
      ring
    · intro i
      constructor
      · apply (lt_div_iff₀ hs).2
        have h := (hx.1 i).1
        linarith only [h]
      · apply (div_lt_iff₀ hs).2
        have h := (hx.1 i).2
        linarith only [h]
    · intro i j hij
      exact (div_lt_div_iff_of_pos_right hs).2 (hx.2 hij)

/-- Centering the finite integer grid does not identify different indices. -/
theorem gridOffset_injective {d : ℕ} (k : ℕ) :
    Function.Injective (gridOffset (d := d) k) := by
  intro j l h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  dsimp only [gridOffset] at hi
  have heq : (j i : ℤ) = (l i : ℤ) := sub_left_injective hi
  exact_mod_cast heq

theorem triangulation_card {d : ℕ} (k : ℕ) :
    (triangulation (d := d) k).card = Nat.factorial d * 3 ^ (k * d) := by
  classical
  change (CoarseDeGiorgi.triangulation (d := d) k).card = _
  have hinj : Function.Injective
      (fun jp : (Fin d → Fin (3 ^ k)) × Equiv.Perm (Fin d) =>
        (gridOffset k jp.1, jp.2)) := by
    intro jp lp h
    have hfst : gridOffset k jp.1 = gridOffset k lp.1 := congrArg Prod.fst h
    have hsnd : jp.2 = lp.2 :=
      congrArg (fun v : (Fin d → ℤ) × Equiv.Perm (Fin d) => v.2) h
    exact Prod.ext (gridOffset_injective k hfst) hsnd
  unfold CoarseDeGiorgi.triangulation
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_perm]
  rw [← pow_mul, Nat.mul_comm]

/-- Every open simplex is an open bounded convex domain. -/
theorem simplexCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ)
    (η : SimplexIndex d k) : IsOpenBoundedConvexDomain (simplexCell k η) := by
  change {v : (Fin d → ℤ) × Equiv.Perm (Fin d) //
    v ∈ CoarseDeGiorgi.triangulation k} at η
  unfold simplexCell CoarseDeGiorgi.simplexCell
  rw [simplex_eq_kuhnSimplex]
  exact Foundations.Simplex.isOpenBoundedConvexDomain_kuhnSimplex _ _ _

/-- Every open simplex is nonempty, including in dimension zero. -/
theorem simplexCell_nonempty {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    (simplexCell k η).Nonempty := by
  change {v : (Fin d → ℤ) × Equiv.Perm (Fin d) //
    v ∈ CoarseDeGiorgi.triangulation k} at η
  unfold simplexCell CoarseDeGiorgi.simplexCell
  rw [simplex_eq_kuhnSimplex]
  exact Foundations.Simplex.nonempty_kuhnSimplex _ _ _

/-- The centered odd grid has exactly symmetric integer endpoints. -/
private theorem grid_half_width (k : ℕ) :
    3 ^ k = 2 * ((3 ^ k - 1) / 2) + 1 := by
  have hodd : Odd (3 ^ k : ℕ) := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow
  obtain ⟨t, ht⟩ := hodd
  omega

private theorem mem_triangulation_iff {d k : ℕ}
    (η : (Fin d → ℤ) × Equiv.Perm (Fin d)) :
    η ∈ CoarseDeGiorgi.triangulation k ↔
      ∃ jp : (Fin d → Fin (3 ^ k)) × Equiv.Perm (Fin d),
        (gridOffset k jp.1, jp.2) = η := by
  simp only [CoarseDeGiorgi.triangulation, Finset.mem_image, Finset.mem_univ, true_and]

/-- Each indexed simplex in the level-k triangulation lies in the unit cube. -/
theorem simplexCell_subset_originCube {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    simplexCell k η ⊆ originCube 1 := by
  classical
  unfold simplexCell CoarseDeGiorgi.simplexCell
  have hη := η.property
  obtain ⟨⟨j, π⟩, heq⟩ := (mem_triangulation_iff (d := d) (k := k) η.1).1 hη
  have hs : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ (-(k : ℤ)) * (3 ^ k : ℕ) = 1 := by
    simp only [zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  have hhalf := grid_half_width k
  have hhalfR : ((3 ^ k : ℕ) : ℝ) = 2 * (((3 ^ k - 1) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhalf
  intro x hx i
  rw [← heq] at hx
  obtain ⟨y, rfl, hy, _⟩ := hx
  have hj0 : (0 : ℝ) ≤ (j i).val := Nat.cast_nonneg _
  have hjhi : ((j i).val : ℝ) ≤ (3 ^ k : ℕ) - 1 := by
    have h : (j i).val + 1 ≤ 3 ^ k := Nat.succ_le_of_lt (j i).isLt
    have hR : ((j i).val : ℝ) + 1 ≤ (3 ^ k : ℕ) := by exact_mod_cast h
    linarith only [hR]
  have hshift0 := mul_nonneg hs.le hj0
  have hshifthi := mul_le_mul_of_nonneg_left hjhi hs.le
  have hylo := mul_lt_mul_of_pos_left (hy i).1 hs
  have hyhi := mul_lt_mul_of_pos_left (hy i).2 hs
  have hmid : (3 : ℝ) ^ (-(k : ℤ)) *
      (((3 ^ k - 1) / 2 : ℕ) : ℝ) = (1 - (3 : ℝ) ^ (-(k : ℤ))) / 2 := by
    nlinarith only [hhalfR, hscale]
  change -(1 / 2 : ℝ) <
      (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) +
        (3 : ℝ) ^ (-(k : ℤ)) * y i ∧
    (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) +
        (3 : ℝ) ^ (-(k : ℤ)) * y i < 1 / 2
  simp only [gridOffset, CoarseDeGiorgi.gridOffset, Int.cast_sub, Int.cast_natCast]
  constructor <;> nlinarith only [hshift0, hshifthi, hylo, hyhi, hmid, hscale]

/-- Coefficient hypotheses restrict from the unit cube to each indexed simplex. -/
theorem weightedCoeffOn_simplexCell {d : ℕ} (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (η : SimplexIndex d k) : IsWeightedCoeffOn (simplexCell k η) a := by
  have hsub := simplexCell_subset_originCube k η
  exact ⟨AEStronglyMeasurable.mono_set hsub ha.1,
    ae_restrict_of_ae_restrict_of_subset hsub ha.2.1,
    ha.2.2.1.mono_set hsub, ha.2.2.2.mono_set hsub⟩

end CoarseDeGiorgi.Moments
