module

public import CoarseDeGiorgi.SharpnessExamples.ScalarProfileLipschitz
public import CoarseDeGiorgi.Weighted.Lipschitz
public import CoarseDeGiorgi.Whitney.ExteriorCells
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped NNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem scalarShiftedRadius_lipschitz {d : ℕ} (c : Vec d) :
    LipschitzWith (Real.toNNReal (Real.sqrt (d : ℝ)))
      (fun x => transverseNorm (x - c)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hpart : transversePart (x - c) - transversePart (y - c) = transversePart (x - y) := by
    funext i
    by_cases hi : i.val = 0 <;> simp [transversePart, hi]
  have hnorm : ‖transversePart (x - y)‖ ≤ ‖x - y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    by_cases hi : i.val = 0
    · simp [transversePart, hi]
    · simpa only [transversePart, hi, ↓reduceIte] using norm_le_pi_norm (x - y) i
  have hdiff : |transverseNorm (x - c) - transverseNorm (y - c)| ≤
      Foundations.Euclid.eNorm2 (transversePart (x - y)) := by
    change |Foundations.Euclid.eNorm2 (transversePart (x - c)) -
      Foundations.Euclid.eNorm2 (transversePart (y - c))| ≤ _
    simp only [Foundations.Euclid.eNorm2_eq_norm_toLp]
    have hb := abs_norm_sub_norm_le (WithLp.toLp 2 (transversePart (x - c)))
      (WithLp.toLp 2 (transversePart (y - c)))
    simpa only [← WithLp.toLp_sub, hpart] using hb
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm]
  exact hdiff.trans ((Foundations.Euclid.eNorm2_le_sqrt_mul_norm _).trans
    (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)))

/-- The cylinder profile is Lipschitz on the closed unit cube. -/
theorem scalarCylinderSubsolution_exists_lipschitzOn {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (scalarCylinderSubsolution (d := d) n ζ)
      (originCube 1) := by
  let V := originCube (d := d) 1
  let f : Vec d → ℝ := fun x => scalarAxialProfile d n ζ (x 0)
  let g : Vec d → ℝ := fun x => scalarRadialProfile d n ζ
    (transverseNorm (x - cylinderCenter (cylinderB n)))
  have hV := CoarseDeGiorgi.Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  have hK : IsCompact (closure V) := hV.isBoundedDomain.isBounded.isCompact_closure
  have hf : ContDiff ℝ (1 : WithTop ℕ∞) f := by
    dsimp [f, scalarAxialProfile]
    fun_prop
  obtain ⟨Kf, hLf⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    hV.convex.closure hK
  obtain ⟨Kg, hLψ⟩ := scalarRadialProfile_exists_lipschitz (n := n) hd hζ0 hζ2
  have hLg := hLψ.comp (scalarShiftedRadius_lipschitz (d := d) (cylinderCenter (cylinderB n)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := CoarseDeGiorgi.Whitney.source_cube_nonempty (d := d) (by norm_num : (0 : ℝ) < 1)
    exact (norm_nonneg _).trans (hM x (subset_closure hx))
  let Lg := Kg * Real.toNNReal (Real.sqrt (d : ℝ))
  let C : ℝ := 2 * (Kf : ℝ) + M * (Lg : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Real.toNNReal C, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hFx : |f x - f y| ≤ (Kf : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using hLf.dist_le_mul x (subset_closure hx) y (subset_closure hy)
  have hGy : |g x - g y| ≤ (Lg : ℝ) * dist x y := by
    simpa only [Real.dist_eq, g, Lg, Function.comp_def] using hLg.dist_le_mul x y
  have hGx : |g x| ≤ 2 := by
    have hb := scalarRadialProfile_bounds (n := n) hd hζ0 hζ2
      (lineRadius_nonneg (x - cylinderCenter (cylinderB n)))
    simpa only [g, abs_of_nonneg hb.1] using hb.2
  have hFy : |f y| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM y (subset_closure hy)
  rw [Real.dist_eq, Real.coe_toNNReal _ hC]
  change |f x * g x - f y * g y| ≤ C * dist x y
  calc
    _ = |(f x - f y) * g x + f y * (g x - g y)| := by congr 1; ring
    _ ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
    _ = |f x - f y| * |g x| + |f y| * |g x - g y| := by rw [abs_mul, abs_mul]
    _ ≤ ((Kf : ℝ) * dist x y) * 2 + M * ((Lg : ℝ) * dist x y) :=
      add_le_add (mul_le_mul hFx hGx (abs_nonneg _) (by positivity))
        (mul_le_mul hFy hGy (abs_nonneg _) hM0)
    _ = C * dist x y := by dsimp [C]; ring

/-- Every per-cylinder profile is in the weighted completion. This uses the
squared-mean-plus-energy completion, with its literal classical gradient. -/
theorem scalarCylinderSubsolution_memH1a {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    MemH1a (scalarSharpnessCoefficient ζ (cylinderRadialConstant d)) (originCube 1)
      (scalarCylinderSubsolution (d := d) n ζ) (smoothGrad (scalarCylinderSubsolution n ζ)) := by
  obtain ⟨K, hLip⟩ := scalarCylinderSubsolution_exists_lipschitzOn hd hζ0 hζ2 n
  exact Weighted.memH1a_of_lipschitzOn
    (CoarseDeGiorgi.Whitney.source_cube_domain (by norm_num))
    (CoarseDeGiorgi.Whitney.source_cube_nonempty (by norm_num))
    (scalarSharpnessCoefficient_isWeightedCoeffOn hd hζ0 hζ2 (cylinderRadialConstant_pos hd))
    hLip (Filter.EventuallyEq.rfl)

end

end CoarseDeGiorgi.SharpnessExamples
