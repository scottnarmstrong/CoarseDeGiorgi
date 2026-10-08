module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Euclid

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Euclidean length, separate from the sup norm on `Vec d`. -/
def eNorm2 (v : Vec d) : ℝ := Real.sqrt (vecNormSq v)

/-- Euclidean distance on the project's coordinate carrier. -/
def eDist2 (x y : Vec d) : ℝ := eNorm2 (x - y)

/-- The local Euclidean length is Mathlib's `PiLp 2` norm. -/
theorem eNorm2_eq_norm_toLp (v : Vec d) :
    eNorm2 v = ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [eNorm2, vecNormSq, vecDot, Real.norm_eq_abs, ← pow_two, sq_abs]

theorem eNorm2_nonneg (v : Vec d) : 0 ≤ eNorm2 v := Real.sqrt_nonneg _

@[simp] theorem eNorm2_zero : eNorm2 (0 : Vec d) = 0 := by
  rw [eNorm2_eq_norm_toLp, WithLp.toLp_zero, norm_zero]

@[simp] theorem eNorm2_eq_zero_iff (v : Vec d) : eNorm2 v = 0 ↔ v = 0 := by
  rw [eNorm2_eq_norm_toLp, norm_eq_zero]
  exact ⟨fun h => congrArg (WithLp.ofLp) h, fun h => h ▸ WithLp.toLp_zero 2⟩

theorem eNorm2_add_le (v w : Vec d) : eNorm2 (v + w) ≤ eNorm2 v + eNorm2 w := by
  simp only [eNorm2_eq_norm_toLp, WithLp.toLp_add]
  exact norm_add_le _ _

theorem eNorm2_smul (c : ℝ) (v : Vec d) : eNorm2 (c • v) = |c| * eNorm2 v := by
  simp only [eNorm2_eq_norm_toLp, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem norm_le_eNorm2 (v : Vec d) : ‖v‖ ≤ eNorm2 v := by
  rw [eNorm2_eq_norm_toLp]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    PiLp.norm_apply_le (WithLp.toLp 2 v) i

theorem eNorm2_le_sqrt_mul_norm (v : Vec d) :
    eNorm2 v ≤ Real.sqrt (d : ℝ) * ‖v‖ := by
  have hsum : vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    calc
      vecNormSq v = ∑ i : Fin d, ‖v i‖ ^ 2 := by
        simp only [vecNormSq, vecDot, Real.norm_eq_abs, ← pow_two, sq_abs]
      _ ≤ ∑ _i : Fin d, ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
      _ = (d : ℝ) * ‖v‖ ^ 2 := by simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
  calc
    eNorm2 v ≤ Real.sqrt ((d : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ‖v‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg v)]

theorem dist_le_eDist2 (x y : Vec d) : dist x y ≤ eDist2 x y := by
  rw [dist_eq_norm, eDist2]
  exact norm_le_eNorm2 _

theorem eDist2_le_sqrt_mul_dist (x y : Vec d) :
    eDist2 x y ≤ Real.sqrt (d : ℝ) * dist x y := by
  rw [dist_eq_norm, eDist2]
  exact eNorm2_le_sqrt_mul_norm _

theorem eDist2_nonneg (x y : Vec d) : 0 ≤ eDist2 x y := eNorm2_nonneg _

@[simp] theorem eDist2_self (x : Vec d) : eDist2 x x = 0 := by
  simp only [eDist2, sub_self, eNorm2_zero]

@[simp] theorem eDist2_eq_zero_iff (x y : Vec d) : eDist2 x y = 0 ↔ x = y := by
  rw [eDist2, eNorm2_eq_zero_iff, sub_eq_zero]

theorem eDist2_pos {x y : Vec d} (h : x ≠ y) : 0 < eDist2 x y :=
  lt_of_le_of_ne (eDist2_nonneg x y) (Ne.symm (mt (eDist2_eq_zero_iff x y).mp h))

theorem eDist2_triangle (x y z : Vec d) : eDist2 x z ≤ eDist2 x y + eDist2 y z := by
  unfold eDist2
  rw [show x - z = (x - y) + (y - z) by abel]
  exact eNorm2_add_le _ _

theorem continuous_eNorm2 : Continuous (eNorm2 (d := d)) := by
  simp only [funext eNorm2_eq_norm_toLp]
  exact continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

theorem continuous_eDist2 : Continuous (fun xy : Vec d × Vec d => eDist2 xy.1 xy.2) :=
  continuous_eNorm2.comp (continuous_fst.sub continuous_snd)

end

end CoarseDeGiorgi.Foundations.Euclid
