import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.CubeCell
import CoarseDeGiorgi.Statements.GridOffset
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Whitney.LiftZeroExtension
import Homogenization.Geometry.ConvexDomain
import Mathlib.Algebra.Ring.Parity

/-! # Triadic cube cells for response moments

Open, bounded, convex and nonempty, contained in `originCube 1`, and weighted-coefficient
restriction for the cubes `cubeCell k j`.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Moments

private theorem originCube_isOpen {d : ℕ} (ρ : ℝ) :
    IsOpen (CoarseDeGiorgi.originCube (d := d) ρ) := by
  have : CoarseDeGiorgi.originCube (d := d) ρ =
      ⋂ i, ({x : Vec d | -(ρ / 2) < x i} ∩ {x : Vec d | x i < ρ / 2}) := by
    ext x; simp [CoarseDeGiorgi.originCube, forall_and]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  exact (isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_apply i) continuous_const)

private theorem cubeCell_eq_preimage {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    CoarseDeGiorgi.cubeCell k j =
      (fun x : Vec d => x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (CoarseDeGiorgi.gridOffset k j i : ℝ)))
        ⁻¹' CoarseDeGiorgi.originCube ((3 : ℝ) ^ (-(k : ℤ))) := rfl

theorem cubeCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    IsOpenBoundedConvexDomain (CoarseDeGiorgi.cubeCell k j) := by
  set c : Vec d := fun i => (3 : ℝ) ^ (-(k : ℤ)) * (CoarseDeGiorgi.gridOffset k j i : ℝ) with hc
  set s : ℝ := (3 : ℝ) ^ (-(k : ℤ)) with hs
  have hs0 : 0 < s := zpow_pos (by norm_num) _
  rw [cubeCell_eq_preimage]
  refine ⟨(originCube_isOpen s).preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · apply Bornology.IsBounded.isBoundedDomain
    refine (Metric.isBounded_closedBall (x := c) (r := s / 2)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have h := hx i
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.sub_apply] at h ⊢
    constructor <;> linarith [h.1, h.2]
  · intro x hx y hy a b ha hb hab i
    have hx' := hx i
    have hy' := hy i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx' hy' ⊢
    have e : a * x i + b * y i - c i = a * (x i - c i) + b * (y i - c i) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rw [e]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this
      constructor <;> nlinarith [hy'.1, hy'.2]
    · constructor <;> nlinarith [hx'.1, hx'.2, hy'.1, hy'.2, mul_pos ha' (sub_pos.2 hx'.1),
        mul_nonneg hb (sub_pos.2 hy'.1).le, mul_pos ha' (sub_pos.2 hx'.2),
        mul_nonneg hb (sub_pos.2 hy'.2).le]

private theorem grid_half_width (k : ℕ) :
    3 ^ k = 2 * ((3 ^ k - 1) / 2) + 1 := by
  have hodd : Odd (3 ^ k : ℕ) := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow
  obtain ⟨t, ht⟩ := hodd
  omega

theorem cubeCell_nonempty {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    (CoarseDeGiorgi.cubeCell k j).Nonempty := by
  have hs0 : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  refine ⟨fun i => (3 : ℝ) ^ (-(k : ℤ)) * (CoarseDeGiorgi.gridOffset k j i : ℝ), ?_⟩
  intro i
  simp only [Pi.sub_apply, sub_self]
  constructor <;> linarith

/-- Each cube cell lies in the unit cube. -/
theorem cubeCell_subset_originCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    CoarseDeGiorgi.cubeCell k j ⊆ CoarseDeGiorgi.originCube 1 := by
  have hs : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ (-(k : ℤ)) * (3 ^ k : ℕ) = 1 := by
    simp only [zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  have hhalfR : ((3 ^ k : ℕ) : ℝ) = 2 * (((3 ^ k - 1) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast grid_half_width k
  intro x hx i
  have hxi := hx i
  simp only [Pi.sub_apply] at hxi
  have hj0 : (0 : ℝ) ≤ (j i).val := Nat.cast_nonneg _
  have hjhi : ((j i).val : ℝ) ≤ (3 ^ k : ℕ) - 1 := by
    have h : (j i).val + 1 ≤ 3 ^ k := Nat.succ_le_of_lt (j i).isLt
    have hR : ((j i).val : ℝ) + 1 ≤ (3 ^ k : ℕ) := by exact_mod_cast h
    linarith only [hR]
  have hshift0 := mul_nonneg hs.le hj0
  have hshifthi := mul_le_mul_of_nonneg_left hjhi hs.le
  have hmid : (3 : ℝ) ^ (-(k : ℤ)) *
      (((3 ^ k - 1) / 2 : ℕ) : ℝ) = (1 - (3 : ℝ) ^ (-(k : ℤ))) / 2 := by
    nlinarith only [hhalfR, hscale]
  simp only [CoarseDeGiorgi.gridOffset, Int.cast_sub, Int.cast_natCast] at hxi
  change -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2
  constructor <;> nlinarith only [hshift0, hshifthi, hxi.1, hxi.2, hmid, hscale]

theorem weightedCoeffOn_cubeCell {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a) (j : Fin d → Fin (3 ^ k)) :
    IsWeightedCoeffOn (CoarseDeGiorgi.cubeCell k j) a :=
  CoarseDeGiorgi.Whitney.lift_coeff_mono ha (cubeCell_subset_originCube k j)

end CoarseDeGiorgi.Moments
