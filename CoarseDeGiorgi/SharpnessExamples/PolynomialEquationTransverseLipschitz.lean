module

public import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationTransverseRegularity
public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxLipschitz
public import CoarseDeGiorgi.Sharpness.LineEquation.LineBasics

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped NNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Every transverse flux coordinate is Lipschitz on the source cube. The
radial scalar factor matches at the interface, and multiplication by a cube
coordinate preserves Lipschitz regularity. -/
theorem polynomialFlux_transverse_lipschitzOn {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ} (he : 0 < epsilon)
    {i : Fin d} (hi : i ≠ 0) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x => polynomialFlux d q t epsilon x i)
      (originCube (d := d) 1) := by
  let V := originCube (d := d) 1
  let ρ : Vec d → ℝ := Sharpness.transverseNorm
  let Q : Vec d → ℝ := fun x => polynomialTransverseFactor d q t epsilon (ρ x)
  let S : ℝ := max (d : ℝ) (2 * epsilon)
  have hV := Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  have hrad (x : Vec d) (hx : x ∈ V) : ρ x ∈ Icc (0 : ℝ) S := by
    refine ⟨Sharpness.lineRadius_nonneg x, ?_⟩
    have hs := Sharpness.transverseNorm_le_sqrt_d_div_two hx
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have hsq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hroot := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_trans (by norm_num) hdR)] at hroot
    have hupper : ρ x ≤ (d : ℝ) := by
      dsimp [ρ]
      linarith
    calc
      ρ x ≤ (d : ℝ) := hupper
      _ ≤ S := by dsimp [S]; exact le_max_left _ _
  obtain ⟨K, hK, hfactor⟩ :=
    polynomialTransverseFactor_lipschitzOn hd q t epsilon S he
      (by dsimp [S]; exact le_max_right _ _)
  have hQbound (x : Vec d) (hx : x ∈ V) (y : Vec d) (hy : y ∈ V) :
      |Q x - Q y| ≤ K * Real.sqrt (d : ℝ) * dist x y := by
    have h := hfactor (ρ x) (hrad x hx) (ρ y) (hrad y hy)
    have hr := transverseNorm_dist_le x y
    dsimp [Q]
    calc
      _ ≤ K * |ρ x - ρ y| := h
      _ ≤ K * (Real.sqrt (d : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left hr hK
      _ = K * Real.sqrt (d : ℝ) * dist x y := by ring
  let KQ : ℝ≥0 := ⟨K * Real.sqrt (d : ℝ), mul_nonneg hK (Real.sqrt_nonneg _)⟩
  have hQ : LipschitzOnWith KQ Q V := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |Q x - Q y| ≤ (KQ : ℝ) * dist x y
    calc
      |Q x - Q y| ≤ K * Real.sqrt (d : ℝ) * dist x y := hQbound x hx y hy
      _ = (KQ : ℝ) * dist x y := by rfl
  have hneg : LipschitzOnWith KQ (fun x => -Q x) V := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |-Q x - -Q y| ≤ (KQ : ℝ) * dist x y
    calc
      |-Q x - -Q y| = |Q x - Q y| := by
        rw [show -Q x - -Q y = -(Q x - Q y) by ring, abs_neg]
      _ ≤ K * Real.sqrt (d : ℝ) * dist x y := hQbound x hx y hy
      _ = (KQ : ℝ) * dist x y := by rfl
  have hcoord : LipschitzOnWith 1 (fun x : Vec d => x i) V := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := norm_le_pi_norm (x - y) i
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm,
      Real.norm_eq_abs, Pi.sub_apply] using h
  obtain ⟨Kprod, hprod⟩ :=
    exists_lipschitzOn_real_mul hV.isBoundedDomain.isBounded hneg hcoord
  refine ⟨Kprod, ?_⟩
  have heq : (fun x : Vec d => polynomialFlux d q t epsilon x i) =
      fun x => -Q x * x i := by
    funext x
    simp [polynomialFlux, hi, Q, ρ]
  rw [heq]
  exact hprod

end

end CoarseDeGiorgi.SharpnessExamples
