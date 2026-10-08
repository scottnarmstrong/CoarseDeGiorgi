import CoarseDeGiorgi.Localization.Geometry
import CoarseDeGiorgi.Foundations.Euclid.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Fixed smooth bumps and the literal quotient partition -/
namespace CoarseDeGiorgi.Localization
open Homogenization Set Metric
open CoarseDeGiorgi.Foundations
open scoped BigOperators Topology ContDiff NNReal
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

/-- A single bump, fixed before the scale and lattice center. -/
def unitBump : ContDiffBump (0 : Vec d) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Translates and dilates of the fixed bump, as in the paper. -/
def localizationBump (m : ℤ) (z : Fin d → ℤ) (x : Vec d) : ℝ :=
  unitBump ((gridSpacing m)⁻¹ • (x - gridCenter m z))

theorem localizationBump_nonneg (m : ℤ) (z : Fin d → ℤ) (x : Vec d) :
    0 ≤ localizationBump m z x := (unitBump (d := d)).nonneg

theorem localizationBump_le_one (m : ℤ) (z : Fin d → ℤ) (x : Vec d) :
    localizationBump m z x ≤ 1 := (unitBump (d := d)).le_one

theorem contDiff_localizationBump (m : ℤ) (z : Fin d → ℤ) :
    ContDiff ℝ ∞ (localizationBump m z) := by
  apply (unitBump (d := d)).contDiff.comp
  fun_prop

theorem localizationBump_eq_one {m : ℤ} {z : Fin d → ℤ} {x : Vec d}
    (hx : x ∈ centralCube m z) : localizationBump m z x = 1 := by
  apply (unitBump (d := d)).one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (gridSpacing_pos m)]
  change (gridSpacing m)⁻¹ * ‖x - gridCenter m z‖ ≤ 1 / 2
  have hh : ‖x - gridCenter m z‖ ≤ gridSpacing m / 2 :=
    (pi_norm_le_iff_of_nonneg (half_pos (gridSpacing_pos m)).le).mpr fun i => by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hx i
  calc
    _ ≤ (gridSpacing m)⁻¹ * (gridSpacing m / 2) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (gridSpacing_pos m).le)
    _ = _ := by field_simp [(gridSpacing_pos m).ne']

theorem support_localizationBump (m : ℤ) (z : Fin d → ℤ) :
    Function.support (localizationBump m z) = ball (gridCenter m z) (gridSpacing m) := by
  ext x
  change unitBump ((gridSpacing m)⁻¹ • (x - gridCenter m z)) ≠ 0 ↔ _
  rw [← Function.mem_support, (unitBump (d := d)).support_eq, mem_ball_zero_iff,
    mem_ball_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (gridSpacing_pos m)]
  change (gridSpacing m)⁻¹ * ‖x - gridCenter m z‖ < 1 ↔ _
  rw [← div_eq_inv_mul, div_lt_one (gridSpacing_pos m)]

theorem tsupport_localizationBump (m : ℤ) (z : Fin d → ℤ) :
    tsupport (localizationBump m z) = closedBall (gridCenter m z) (gridSpacing m) := by
  rw [tsupport, support_localizationBump, closure_ball _ (gridSpacing_pos m).ne']


/-- Every bump keeps the source's half-spacing separation from the auxiliary-cube complement. -/
theorem localizationBump_separation {m : ℤ} {z : Fin d → ℤ} {x : Vec d}
    (hx : x ∈ tsupport (localizationBump m z)) {y : Vec d} (hy : y ∉ auxCube m z) :
    gridSpacing m / 2 ≤ Euclid.eDist2 x y := by
  rw [tsupport_localizationBump, mem_closedBall_iff_norm] at hx
  rw [auxCube_eq_coordinates] at hy
  obtain ⟨i, hi⟩ := not_forall.mp hy
  have hi' : 3 * gridSpacing m / 2 ≤ |y i - gridCenter m z i| := not_lt.mp hi
  have hcoord : |x i - gridCenter m z i| ≤ ‖x - gridCenter m z‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - gridCenter m z) i
  have hxi : |x i - gridCenter m z i| ≤ gridSpacing m := hcoord.trans hx
  have hxy : |x i - y i| ≤ Euclid.eDist2 x y := by
    calc
      _ ≤ ‖x - y‖ := by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
      _ ≤ Euclid.eDist2 x y := Euclid.norm_le_eNorm2 (x - y)
  have hh := abs_sub_le (y i) (x i) (gridCenter m z i)
  rw [abs_sub_comm (y i) (x i)] at hh
  linarith only [hh, hi', hxi, hxy]

/-- Smooth switch, zero up to one half and one from three quarters onward. -/
def localizationSwitch (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 2)

theorem localizationSwitch_nonneg (t : ℝ) : 0 ≤ localizationSwitch t :=
  Real.smoothTransition.nonneg _

theorem localizationSwitch_le_one (t : ℝ) : localizationSwitch t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem localizationSwitch_eq_zero {t : ℝ} (ht : t ≤ 1 / 2) : localizationSwitch t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [ht])

theorem localizationSwitch_eq_one {t : ℝ} (ht : 3 / 4 ≤ t) : localizationSwitch t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith only [ht])

/-- The real division convention gives zero at a zero denominator. -/
def localizationFactor (t : ℝ) : ℝ := localizationSwitch t / t

/-- Sum of the chosen nonnegative bumps. -/
def bumpSum (m : ℤ) (Z : Finset (Fin d → ℤ)) (x : Vec d) : ℝ :=
  ∑ z ∈ Z, localizationBump m z x

/-- Literal source quotient, including its zero-denominator convention. -/
def localizationPartition (m : ℤ) (Z : Finset (Fin d → ℤ)) (z : Fin d → ℤ) (x : Vec d) : ℝ :=
  localizationBump m z x * localizationFactor (bumpSum m Z x)

@[simp] theorem localizationFactor_zero : localizationFactor 0 = 0 := by
  simp only [localizationFactor, div_zero]

theorem bumpSum_nonneg (m : ℤ) (Z : Finset (Fin d → ℤ)) (x : Vec d) : 0 ≤ bumpSum m Z x :=
  Finset.sum_nonneg fun z _ => localizationBump_nonneg m z x

theorem localizationPartition_nonneg (m : ℤ) (Z : Finset (Fin d → ℤ))
    (z : Fin d → ℤ) (x : Vec d) : 0 ≤ localizationPartition m Z z x :=
  mul_nonneg (localizationBump_nonneg _ _ _) (div_nonneg (localizationSwitch_nonneg _) (bumpSum_nonneg _ _ _))

theorem localizationPartition_bound {m : ℤ} {Z : Finset (Fin d → ℤ)} {z : Fin d → ℤ}
    (hz : z ∈ Z) (x : Vec d) : |localizationPartition m Z z x| ≤ 1 := by
  rw [abs_of_nonneg (localizationPartition_nonneg _ _ _ _)]
  have hle : localizationBump m z x ≤ bumpSum m Z x :=
    Finset.single_le_sum (fun j _ => localizationBump_nonneg m j x) hz
  by_cases hzero : bumpSum m Z x = 0
  · simp only [localizationPartition, hzero, localizationFactor_zero, mul_zero, zero_le_one]
  have hpos : 0 < bumpSum m Z x := (bumpSum_nonneg _ _ _).lt_of_ne' hzero
  unfold localizationPartition localizationFactor
  rw [← mul_div_assoc]
  apply (div_le_one hpos).mpr
  exact (mul_le_mul_of_nonneg_left (localizationSwitch_le_one _) (localizationBump_nonneg _ _ _)).trans (by simpa only [mul_one] using hle)

theorem support_localizationPartition_subset (m : ℤ) (Z : Finset (Fin d → ℤ)) (z : Fin d → ℤ) :
    Function.support (localizationPartition m Z z) ⊆ Function.support (localizationBump m z) := by
  intro x hx hzero
  exact hx (by simp only [localizationPartition, hzero, zero_mul])

theorem sum_localizationPartition_eq_one {m : ℤ} {Z : Finset (Fin d → ℤ)} {x : Vec d}
    (hx : 3 / 4 ≤ bumpSum m Z x) : (∑ z ∈ Z, localizationPartition m Z z x) = 1 := by
  simp only [localizationPartition, ← Finset.sum_mul, localizationFactor, localizationSwitch_eq_one hx]
  change bumpSum m Z x * (1 / bumpSum m Z x) = 1
  exact mul_one_div_cancel (by linarith only [hx])

/-- The removable division at zero is smooth because the numerator vanishes nearby. -/
theorem contDiff_localizationFactor : ContDiff ℝ ∞ localizationFactor := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < 1 / 2
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) t).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds ht] with u hu
    simp only [localizationFactor, localizationSwitch_eq_zero hu.le, zero_div]
  · have ht0 : t ≠ 0 := by linarith only [not_lt.mp ht]
    exact (Real.smoothTransition.contDiffAt.comp t
      (contDiffAt_const.mul contDiffAt_id |>.sub contDiffAt_const)).div contDiffAt_id ht0

theorem contDiff_bumpSum (m : ℤ) (Z : Finset (Fin d → ℤ)) : ContDiff ℝ ∞ (bumpSum m Z) :=
  ContDiff.sum fun z _ => contDiff_localizationBump m z

theorem contDiff_localizationPartition (m : ℤ) (Z : Finset (Fin d → ℤ)) (z : Fin d → ℤ) :
    ContDiff ℝ ∞ (localizationPartition m Z z) :=
  (contDiff_localizationBump m z).mul (contDiff_localizationFactor.comp (contDiff_bumpSum m Z))


theorem localizationPartition_separation {m : ℤ} {Z : Finset (Fin d → ℤ)} {z : Fin d → ℤ}
    {x : Vec d} (hx : x ∈ tsupport (localizationPartition m Z z)) {y : Vec d}
    (hy : y ∉ auxCube m z) : gridSpacing m / 2 ≤ Euclid.eDist2 x y := by
  apply localizationBump_separation _ hy
  exact closure_mono (support_localizationPartition_subset m Z z) hx

/-- The finite sum is at least one at every point of the selected target. -/
theorem one_le_bumpSum_on_target {m : ℤ} (hs1 : gridSpacing m ≤ 1)
    {K : Set (Vec d)} (hK : ∀ y ∈ K, ∀ i, |y i| ≤ 1 / 2) {x : Vec d} (hx : x ∈ K) :
    1 ≤ bumpSum m (coverIndices m K) x := by
  obtain ⟨z, hz, hzc⟩ := coverIndices_covers hs1 hK hx
  calc
    1 = localizationBump m z x := (localizationBump_eq_one hzc).symm
    _ ≤ _ := Finset.single_le_sum (fun j _ => localizationBump_nonneg m j x) hz

/-- Equality on an open neighborhood of the entire closed target, not just on the target. -/
theorem exists_open_partition_neighborhood {m : ℤ} (hs1 : gridSpacing m ≤ 1)
    {K : Set (Vec d)} (hK : ∀ y ∈ K, ∀ i, |y i| ≤ 1 / 2) :
    ∃ U : Set (Vec d), IsOpen U ∧ K ⊆ U ∧
      ∀ x ∈ U, (∑ z ∈ coverIndices m K, localizationPartition m (coverIndices m K) z x) = 1 := by
  refine ⟨{x | 3 / 4 < bumpSum m (coverIndices m K) x}, ?_, ?_, ?_⟩
  · exact isOpen_lt continuous_const (contDiff_bumpSum m (coverIndices m K)).continuous
  · intro x hx
    exact lt_of_lt_of_le (by norm_num : (3 : ℝ) / 4 < 1) (one_le_bumpSum_on_target hs1 hK hx)
  · intro x hx
    exact sum_localizationPartition_eq_one hx.le

/-- Fixed smooth compactly supported bump has a finite Lipschitz constant. -/
theorem exists_unitBump_lipschitz : ∃ L : ℝ≥0, LipschitzWith L (unitBump (d := d)) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (unitBump (d := d)).hasCompactSupport
    (unitBump (d := d)).contDiff (by norm_num : (∞ : ℕ∞ω) ≠ 0)

/-- A single constant is chosen before all grid scales and lattice centers. -/
theorem exists_localizationBump_difference_bound : ∃ L : ℝ, 0 < L ∧
    ∀ (m : ℤ) (z : Fin d → ℤ) (x y : Vec d),
      |localizationBump m z x - localizationBump m z y| ≤
        (L / gridSpacing m) * dist x y := by
  obtain ⟨L, hL⟩ := exists_unitBump_lipschitz (d := d)
  refine ⟨(L : ℝ) + 1, by positivity, ?_⟩
  intro m z x y
  have hh := hL.dist_le_mul ((gridSpacing m)⁻¹ • (x - gridCenter m z))
    ((gridSpacing m)⁻¹ • (y - gridCenter m z))
  rw [Real.dist_eq, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos (gridSpacing_pos m)] at hh
  change |localizationBump m z x - localizationBump m z y| ≤ _
  have he : (L : ℝ) * ((gridSpacing m)⁻¹ * ‖x - y‖) = ((L : ℝ) / gridSpacing m) * dist x y := by
    rw [dist_eq_norm]
    ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by linarith : (L : ℝ) ≤ (L : ℝ) + 1) (gridSpacing_pos m).le)
    dist_nonneg)

end
end CoarseDeGiorgi.Localization


