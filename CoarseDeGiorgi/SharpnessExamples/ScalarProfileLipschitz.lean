module

public import CoarseDeGiorgi.SharpnessExamples.ScalarProfileCalculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

open Homogenization MeasureTheory Set
open scoped NNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private def scalarClamp (a b r : ℝ) : ℝ := min (max r a) b

private theorem scalarClamp_mem {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    scalarClamp a b r ∈ Icc a b :=
  ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩

private theorem scalarClamp_lipschitz (a b : ℝ) :
    LipschitzWith 1 (scalarClamp a b) :=
  (LipschitzWith.id.max_const a).min_const b

private theorem realMul_lipschitz (c : ℝ) :
    LipschitzWith ‖c‖₊ (fun r : ℝ => c * r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, ← mul_sub, abs_mul, coe_nnnorm, Real.norm_eq_abs]
  exact le_rfl

private theorem annularProfile_lipschitzOn {d : ℕ} (hd : 3 ≤ d) :
    LipschitzOnWith (Real.toNNReal (cylinderRadialConstant d))
      (scalarAnnularProfile d) (Icc 1 2) := by
  have hκ := cylinderRadialConstant_pos hd
  apply (convex_Icc (1 : ℝ) 2).lipschitzOnWith_of_nnnorm_deriv_le
  · intro r hr
    exact (scalarAnnularProfile_hasDerivAt d (by linarith [hr.1])).differentiableAt
  · intro r hr
    have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hr0 : 0 < r := by linarith [hr.1]
    have hderiv := (scalarAnnularProfile_hasDerivAt d hr0).deriv
    have hpow : Real.rpow r (2 - (d : ℝ)) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hr.1 (by linarith)
    have hrp : 0 ≤ Real.rpow r (2 - (d : ℝ)) := Real.rpow_nonneg hr0.le _
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hκ.le, hderiv,
      Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hκ,
      abs_of_nonneg hrp]
    exact mul_le_of_le_one_right hκ.le hpow

private theorem quadraticProfile_lipschitzOn :
    LipschitzOnWith 2 (fun r : ℝ => 1 - r ^ 2) (Icc 0 1) := by
  apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
  · intro r _
    fun_prop
  · intro r hr
    have hderiv : deriv (fun t : ℝ => 1 - t ^ 2) r = 0 - (2 : ℝ) * r := by
      simpa only [Pi.sub_def, Nat.cast_ofNat, Nat.reduceSub, pow_one] using
        ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_pow 2 r)).deriv
    rw [← NNReal.coe_le_coe, coe_nnnorm, hderiv]
    norm_num only [Nat.cast_ofNat, pow_one, zero_sub, norm_neg, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg hr.1]
    norm_num
    linarith [hr.2]

/-- A clamped representation of the profile makes its global Lipschitz
regularity independent of the two derivative jumps. -/
private theorem radialProfile_eq_clamps {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (r : ℝ) :
    scalarRadialProfile d n ζ r =
      scalarAnnularProfile d (scalarClamp 1 2
        (r / cylinderRadius d n ζ (cylinderRadialConstant d))) +
      scalarProfileXi d n ζ * (1 - (scalarClamp 0 1
        (r / cylinderRadius d n ζ (cylinderRadialConstant d))) ^ 2) := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε : 0 < ε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  change scalarRadialProfile d n ζ r = scalarAnnularProfile d (scalarClamp 1 2 (r / ε)) +
    scalarProfileXi d n ζ * (1 - (scalarClamp 0 1 (r / ε)) ^ 2)
  by_cases hr : r ≤ ε
  · have hratio : r / ε ≤ 1 := (div_le_one hε).2 hr
    have hcl1 : scalarClamp 1 2 (r / ε) = 1 := by
      simp [scalarClamp, max_eq_right hratio]
    rw [hcl1, scalarAnnularProfile_one hd]
    dsimp only [ε] at hr
    simp only [scalarRadialProfile, hr, ↓reduceIte]
    by_cases hr0 : 0 ≤ r
    · have hratio0 : 0 ≤ r / ε := div_nonneg hr0 hε.le
      rw [max_eq_left hr0]
      simp only [scalarClamp, max_eq_left hratio0, min_eq_left hratio]
      rw [div_pow]
    · have hratio0 : r / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr0) hε.le
      simp [scalarClamp, max_eq_right hratio0, max_eq_right (le_of_not_ge hr0)]
  · have hratio : 1 ≤ r / ε := (one_le_div hε).2 (le_of_not_ge hr)
    have hcl0 : scalarClamp 0 1 (r / ε) = 1 := by
      simp [scalarClamp, max_eq_left (by linarith : 0 ≤ r / ε), min_eq_right hratio]
    rw [hcl0]
    simp only [one_pow, sub_self, mul_zero, add_zero]
    by_cases hr2 : r < 2 * ε
    · have hratio2 : r / ε ≤ 2 := (div_le_iff₀ hε).2 hr2.le
      have hcl1 : scalarClamp 1 2 (r / ε) = r / ε := by
        simp [scalarClamp, max_eq_left hratio, min_eq_left hratio2]
      rw [hcl1]
      dsimp only [ε] at hr hr2 ⊢
      simp only [scalarRadialProfile, hr, hr2, ↓reduceIte]
    · have hratio2 : 2 ≤ r / ε := (le_div_iff₀ hε).2 (le_of_not_gt hr2)
      have hcl1 : scalarClamp 1 2 (r / ε) = 2 := by
        simp [scalarClamp, max_eq_left hratio, min_eq_right hratio2]
      rw [hcl1, scalarAnnularProfile_two]
      dsimp only [ε] at hr hr2 ⊢
      simp only [scalarRadialProfile, hr, hr2, ↓reduceIte]

/-- The radial profile is globally Lipschitz, including both interfaces. -/
theorem scalarRadialProfile_exists_lipschitz {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    ∃ K : ℝ≥0, LipschitzWith K (scalarRadialProfile d n ζ) := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  let R : ℝ → ℝ := fun r => ε⁻¹ * r
  have hR : LipschitzWith ‖ε⁻¹‖₊ R := realMul_lipschitz _
  let A : ℝ → ℝ := fun r => scalarClamp 1 2 (R r)
  let B : ℝ → ℝ := fun r => scalarClamp 0 1 (R r)
  have hA : LipschitzWith ‖ε⁻¹‖₊ A := by
    simpa only [one_mul, A, Function.comp_def] using (scalarClamp_lipschitz 1 2).comp hR
  have hB : LipschitzWith ‖ε⁻¹‖₊ B := by
    simpa only [one_mul, B, Function.comp_def] using (scalarClamp_lipschitz 0 1).comp hR
  have hAnn : LipschitzWith (Real.toNNReal (cylinderRadialConstant d) * ‖ε⁻¹‖₊)
      (fun r => scalarAnnularProfile d (A r)) := by
    rw [← lipschitzOnWith_univ]
    exact (annularProfile_lipschitzOn hd).comp hA.lipschitzOnWith
      (fun r _ => scalarClamp_mem (by norm_num) (R r))
  have hQuad : LipschitzWith (2 * ‖ε⁻¹‖₊) (fun r => 1 - (B r) ^ 2) := by
    rw [← lipschitzOnWith_univ]
    exact quadraticProfile_lipschitzOn.comp hB.lipschitzOnWith
      (fun r _ => scalarClamp_mem (by norm_num) (R r))
  have hXi := (realMul_lipschitz (scalarProfileXi d n ζ)).comp hQuad
  refine ⟨Real.toNNReal (cylinderRadialConstant d) * ‖ε⁻¹‖₊ +
    ‖scalarProfileXi d n ζ‖₊ * (2 * ‖ε⁻¹‖₊), ?_⟩
  have heq : scalarRadialProfile d n ζ = fun r =>
      scalarAnnularProfile d (A r) + scalarProfileXi d n ζ * (1 - (B r) ^ 2) := by
    funext r
    rw [radialProfile_eq_clamps hd hζ0 hζ2]
    dsimp [A, B, R]
    simp only [div_eq_mul_inv, mul_comm]
    rfl
  rw [heq]
  exact hAnn.add hXi

end

end CoarseDeGiorgi.SharpnessExamples
