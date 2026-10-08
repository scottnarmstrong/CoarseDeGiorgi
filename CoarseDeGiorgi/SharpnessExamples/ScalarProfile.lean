module

public import CoarseDeGiorgi.SharpnessExamples.ScalarIntegrability
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The radial and axial profiles in Theorem F

Index `n` denotes manuscript index `j = n + 1`. The annular profile is kept
as its defining integral, so its flux derivative agrees exactly with the
source. All interfaces use their continuous values.
-/

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Relative quadratic correction in the core. -/
def scalarProfileXi (d n : ℕ) (ζ : ℝ) : ℝ :=
  cylinderRadialConstant d / 2 *
    (cylinderRadius d n ζ (cylinderRadialConstant d) / cylinderB n) ^ 2

/-- The normalized radial harmonic profile on the annulus. -/
def scalarAnnularProfile (d : ℕ) (r : ℝ) : ℝ :=
  cylinderRadialConstant d * ∫ z in r..2, Real.rpow z (2 - (d : ℝ))

/-- The source's radial profile, constant on the negative half line. -/
def scalarRadialProfile (d n : ℕ) (ζ r : ℝ) : ℝ :=
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  if r ≤ ε then 1 + scalarProfileXi d n ζ * (1 - (max r 0) ^ 2 / ε ^ 2)
  else if r < 2 * ε then scalarAnnularProfile d (r / ε) else 0

/-- Axial factor in cylinder n. -/
def scalarAxialProfile (d n : ℕ) (ζ t : ℝ) : ℝ :=
  (n + 1 : ℕ) / (1 + scalarProfileXi d n ζ) *
    Real.cosh (cylinderRate d n (cylinderRadialConstant d) * t)

/-- The per-cylinder nonnegative subsolution before taking its sum. -/
def scalarCylinderSubsolution {d : ℕ} [NeZero d] (n : ℕ) (ζ : ℝ)
    (x : Vec d) : ℝ :=
  scalarAxialProfile d n ζ (x 0) * scalarRadialProfile d n ζ
    (transverseNorm (x - cylinderCenter (cylinderB n)))

/-- Normalization of the radial harmonic integral. -/
theorem scalarAnnularProfile_one {d : ℕ} (hd : 3 ≤ d) :
    scalarAnnularProfile d 1 = 1 := by
  unfold scalarAnnularProfile cylinderRadialConstant
  by_cases hd3 : d = 3
  · subst d
    simp only [↓reduceIte, Nat.cast_ofNat]
    have hfun : (fun z : ℝ => Real.rpow z (2 - 3)) = (fun z => z⁻¹) := by
      funext z
      norm_num only [show (2 - 3 : ℝ) = -1 by norm_num]
      exact Real.rpow_neg_one z
    rw [hfun, integral_inv_of_pos (by norm_num) (by norm_num)]
    simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  · have hdim : (3 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 3 < d)
    have hpow : Real.rpow 2 (3 - (d : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    change (2 : ℝ) ^ (3 - (d : ℝ)) < 1 at hpow
    have hnot : (2 - (d : ℝ)) ≠ -1 := by linarith
    have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) 2 := by norm_num
    simp only [hd3, ↓reduceIte, Real.rpow_eq_pow]
    rw [integral_rpow (Or.inr ⟨hnot, hzero⟩)]
    have hexp : (2 - (d : ℝ)) + 1 = 3 - (d : ℝ) := by ring
    rw [hexp, Real.one_rpow]
    field_simp [ne_of_gt (by linarith : (d : ℝ) - 3 > 0),
      ne_of_gt (by linarith : 1 - (2 : ℝ) ^ (3 - (d : ℝ)) > 0),
      ne_of_lt (by linarith : 3 - (d : ℝ) < 0)]
    ring

theorem scalarAnnularProfile_two (d : ℕ) : scalarAnnularProfile d 2 = 0 := by
  simp [scalarAnnularProfile]

/-- The annular branch decreases from one to zero. -/
theorem scalarAnnularProfile_bounds {d : ℕ} (hd : 3 ≤ d) {r : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ scalarAnnularProfile d r ∧ scalarAnnularProfile d r ≤ 1 := by
  have hκ := cylinderRadialConstant_pos hd
  have hf : IntervalIntegrable (fun z : ℝ => Real.rpow z (2 - (d : ℝ))) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    have hx1 : 1 ≤ x := by simpa using hx.1
    change x ≠ 0
    linarith
  have hnonneg : ∀ z ∈ Icc (1 : ℝ) 2, 0 ≤ Real.rpow z (2 - (d : ℝ)) :=
    fun z hz => Real.rpow_nonneg (by linarith [hz.1]) _
  constructor
  · exact mul_nonneg hκ.le (intervalIntegral.integral_nonneg hr2
      (fun z hz => Real.rpow_nonneg (by linarith [hz.1]) _))
  · rw [← scalarAnnularProfile_one hd]
    apply mul_le_mul_of_nonneg_left _ hκ.le
    apply intervalIntegral.integral_mono_interval hr1 hr2 le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      exact hnonneg z ⟨hz.1.le, hz.2⟩
    · exact hf

/-- The separation condition makes the relative core correction less than one. -/
theorem scalarProfileXi_bounds {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    0 < scalarProfileXi d n ζ ∧ scalarProfileXi d n ζ < 1 := by
  let κ := cylinderRadialConstant d
  let ε := cylinderRadius d n ζ κ
  let b := cylinderB n
  have hκ : 0 < κ := cylinderRadialConstant_pos hd
  have hε : 0 < ε := (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1
  have hb : 0 < b := cylinderB_pos n
  have hsep : ε < b / (16 * (1 + Real.sqrt κ)) :=
    (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).2.1
  have hroot : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hsq := Real.sq_sqrt hκ.le
  have hratio : ε / b < 1 / (16 * (1 + Real.sqrt κ)) := by
    apply (div_lt_iff₀ hb).2
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hsep
  have hsmall : Real.sqrt κ * (ε / b) < 1 / 16 := by
    have hden : 0 < 16 * (1 + Real.sqrt κ) := by positivity
    have hbound : Real.sqrt κ / (16 * (1 + Real.sqrt κ)) < 1 / 16 := by
      apply (div_lt_iff₀ hden).2
      nlinarith
    exact (mul_lt_mul_of_pos_left hratio hroot).trans (by
      simpa only [div_eq_mul_inv, one_mul] using hbound)
  change 0 < κ / 2 * (ε / b) ^ 2 ∧ κ / 2 * (ε / b) ^ 2 < 1
  constructor
  · positivity
  · have hnonneg : 0 ≤ Real.sqrt κ * (ε / b) := by positivity
    nlinarith only [hsq, hsmall, hnonneg, sq_nonneg (Real.sqrt κ * (ε / b))]

/-- The core branch lies between one and `1 + ξ`. -/
theorem scalarRadialProfile_core_bounds {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hr0 : 0 ≤ r)
    (hr : r ≤ cylinderRadius d n ζ (cylinderRadialConstant d)) :
    1 ≤ scalarRadialProfile d n ζ r ∧
      scalarRadialProfile d n ζ r ≤ 1 + scalarProfileXi d n ζ := by
  have hξ := scalarProfileXi_bounds (n := n) hd hζ0 hζ2
  have hε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  have hratio : r ^ 2 / (cylinderRadius d n ζ (cylinderRadialConstant d)) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hε)).2
    exact (sq_le_sq₀ hr0 hε.le).2 hr
  have hratio0 : 0 ≤ r ^ 2 / (cylinderRadius d n ζ (cylinderRadialConstant d)) ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  simp only [scalarRadialProfile, hr, ↓reduceIte, max_eq_left hr0]
  constructor <;> nlinarith only [hξ.1, hratio, hratio0]

/-- The whole radial profile is nonnegative and at most two. -/
theorem scalarRadialProfile_bounds {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hr0 : 0 ≤ r) :
    0 ≤ scalarRadialProfile d n ζ r ∧ scalarRadialProfile d n ζ r ≤ 2 := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε : 0 < ε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  by_cases hr : r ≤ ε
  · have hb := scalarRadialProfile_core_bounds hd hζ0 hζ2 hr0 hr
    have hξ := scalarProfileXi_bounds (n := n) hd hζ0 hζ2
    exact ⟨(by linarith [hb.1]), (by linarith [hb.2, hξ.2])⟩
  · by_cases hr2 : r < 2 * ε
    · have hratio1 : 1 ≤ r / ε := (one_le_div hε).2 (le_of_not_ge hr)
      have hratio2 : r / ε ≤ 2 := (div_le_iff₀ hε).2 (by linarith)
      have hb := scalarAnnularProfile_bounds hd hratio1 hratio2
      dsimp only [ε] at hr hr2 hb
      simp only [scalarRadialProfile, hr, hr2, ↓reduceIte]
      exact ⟨hb.1, hb.2.trans (by norm_num)⟩
    · dsimp only [ε] at hr hr2
      simp [scalarRadialProfile, hr, hr2]

/-- The profile vanishes on and beyond the outer interface. -/
theorem scalarRadialProfile_eq_zero {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hr : 2 * cylinderRadius d n ζ (cylinderRadialConstant d) ≤ r) :
    scalarRadialProfile d n ζ r = 0 := by
  have hε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  have hnot : ¬ r ≤ cylinderRadius d n ζ (cylinderRadialConstant d) := by linarith
  simp [scalarRadialProfile, hnot, not_lt.mpr hr]

/-- The axial factor has the positive lower bound used on every core. -/
theorem scalarAxialProfile_lower {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (t : ℝ) :
    ((n + 1 : ℕ) : ℝ) / 2 ≤ scalarAxialProfile d n ζ t := by
  have hξ := scalarProfileXi_bounds (n := n) hd hζ0 hζ2
  have hden : 0 < 1 + scalarProfileXi d n ζ := by linarith [hξ.1]
  have hj : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfrac : ((n + 1 : ℕ) : ℝ) / 2 ≤
      ((n + 1 : ℕ) : ℝ) / (1 + scalarProfileXi d n ζ) :=
    div_le_div_of_nonneg_left hj hden (by linarith [hξ.2])
  unfold scalarAxialProfile
  exact hfrac.trans (le_mul_of_one_le_right (div_nonneg hj hden.le) (Real.one_le_cosh _))

theorem scalarCylinderSubsolution_nonneg {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) (x : Vec d) :
    0 ≤ scalarCylinderSubsolution n ζ x := by
  unfold scalarCylinderSubsolution
  exact mul_nonneg ((div_nonneg (Nat.cast_nonneg _) (by norm_num)).trans
    (scalarAxialProfile_lower hd hζ0 hζ2 _))
    (scalarRadialProfile_bounds hd hζ0 hζ2 (lineRadius_nonneg _)).1

/-- On the nth core the subsolution has height at least `(n+1)/2`. -/
theorem scalarCylinderSubsolution_core_lower {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) {n : ℕ} {x : Vec d}
    (hx : x ∈ scalarCoreBand n ζ (cylinderRadialConstant d)) :
    ((n + 1 : ℕ) : ℝ) / 2 ≤ scalarCylinderSubsolution n ζ x := by
  have hX := scalarAxialProfile_lower (n := n) hd hζ0 hζ2 (x 0)
  have hX0 : 0 ≤ scalarAxialProfile d n ζ (x 0) :=
    (div_nonneg (Nat.cast_nonneg _) (by norm_num)).trans hX
  have hψ := scalarRadialProfile_core_bounds hd hζ0 hζ2 (lineRadius_nonneg _)
    (le_of_lt hx)
  exact hX.trans (le_mul_of_one_le_right hX0 hψ.1)

end

end CoarseDeGiorgi.SharpnessExamples
