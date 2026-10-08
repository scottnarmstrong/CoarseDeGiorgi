import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationInterface
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import CoarseDeGiorgi.Sharpness.LineEquation.CutoffLimit
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Homogenization MeasureTheory Set Filter
open Topology
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- In the open inner region, the radial profile has its polynomial derivative. -/
theorem polynomialProfile_hasDerivAt_inner {d : ℕ} (q t epsilon r : ℝ)
    (_he : 0 < epsilon) (hr : r < 2 * epsilon) :
    HasDerivAt (polynomialProfile d q t epsilon) (2 * r / epsilon ^ 2) r := by
  have hlocal : ∀ᶠ s in 𝓝 r, s < 2 * epsilon := Iio_mem_nhds hr
  have heq : polynomialProfile d q t epsilon =ᶠ[𝓝 r]
      fun s => s ^ 2 / epsilon ^ 2 := by
    filter_upwards [hlocal] with s hs
    simp [polynomialProfile, le_of_lt hs]
  have hpoly : HasDerivAt (fun s : ℝ => s ^ 2 / epsilon ^ 2)
      (2 * r / epsilon ^ 2) r := by
    convert ((hasDerivAt_id r).pow 2).div_const (epsilon ^ 2) using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  exact hpoly.congr_of_eventuallyEq heq

/-- Outside the interface, the profile derivative is the prescribed radial
continuation. -/
theorem polynomialProfile_hasDerivAt_outer {d : ℕ} (q t epsilon r : ℝ)
    (he : 0 < epsilon) (hr : 2 * epsilon < r) :
    HasDerivAt (polynomialProfile d q t epsilon)
      (polynomialOuterDerivative d q t epsilon r) r := by
  let R := 2 * epsilon
  have hR : 0 < R := by dsimp [R]; positivity
  have hlocal : ∀ᶠ s in 𝓝 r, R < s := Ioi_mem_nhds (by dsimp [R]; exact hr)
  have hrpos : 0 < r := by linarith [he]
  have heq : polynomialProfile d q t epsilon =ᶠ[𝓝 r]
      fun s => 4 + ∫ z in R..s, polynomialOuterDerivative d q t epsilon z := by
    filter_upwards [hlocal] with s hs
    simp [polynomialProfile, R, not_le_of_gt hs]
  have hDcontOn : ContinuousOn (polynomialOuterDerivative d q t epsilon) (Ioi 0) := by
    have hbase (p : ℝ) : ContinuousOn (fun z : ℝ => Real.rpow z p) (Ioi 0) := by
      intro z hz
      exact (Real.continuousAt_rpow_const z p (Or.inl (ne_of_gt hz))).continuousWithinAt
    have hA : ContinuousOn (fun _ : ℝ =>
        2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2) (Ioi 0) := continuousOn_const
    have hB : ContinuousOn (fun z : ℝ =>
        2 / ((d : ℝ) - 1) *
          (Real.rpow z ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1))) (Ioi 0) :=
      continuousOn_const.mul ((hbase _).sub continuousOn_const)
    change ContinuousOn (fun z : ℝ => Real.rpow z (2 - (d : ℝ)) *
      (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
        epsilon ^ 2 +
       2 / ((d : ℝ) - 1) *
        (Real.rpow z ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1)))) (Ioi 0)
    exact (hbase _).mul (hA.add hB)
  have hDsm : StronglyMeasurableAtFilter (polynomialOuterDerivative d q t epsilon)
      (𝓝 r) volume := hDcontOn.stronglyMeasurableAtFilter isOpen_Ioi r hrpos
  have hDcont : ContinuousAt (polynomialOuterDerivative d q t epsilon) r :=
    hDcontOn.continuousAt (Ioi_mem_nhds hrpos)
  have hInt : IntervalIntegrable (polynomialOuterDerivative d q t epsilon)
      volume R r := by
    have hcont : ContinuousOn (polynomialOuterDerivative d q t epsilon) (uIcc R r) := by
      rw [uIcc_of_le (le_of_lt (by dsimp [R] at hr ⊢; linarith))]
      apply hDcontOn.mono
      intro z hz
      have hzR : R ≤ z := hz.1
      have hzpos : 0 < z := by dsimp [R] at hzR; linarith [he]
      exact hzpos
    exact hcont.intervalIntegrable (μ := volume)
  have hfund := intervalIntegral.integral_hasDerivAt_right hInt hDsm hDcont
  have hmain : HasDerivAt
      (fun s => 4 + ∫ z in R..s, polynomialOuterDerivative d q t epsilon z)
      (polynomialOuterDerivative d q t epsilon r) r := by
    convert (hasDerivAt_const r 4).add hfund using 1
    simp
  exact hmain.congr_of_eventuallyEq heq

/-- The classical coordinate gradient formula away from the transverse axis
and the coefficient interface. -/
theorem polynomialSolution_smoothGrad_formula {d : ℕ} [NeZero d]
    (q t epsilon : ℝ) (he : 0 < epsilon) {x : Vec d}
    (hr : 0 < Sharpness.transverseNorm x)
    (hinner : Sharpness.transverseNorm x < 2 * epsilon ∨
      2 * epsilon < Sharpness.transverseNorm x) (i : Fin d) :
    smoothGrad (polynomialSolution d q t epsilon) x i =
      if i = 0 then 2 * x 0 else
        -deriv (polynomialProfile d q t epsilon) (Sharpness.transverseNorm x) *
          (x i / Sharpness.transverseNorm x) := by
  let r := Sharpness.transverseNorm x
  have hψdiff : DifferentiableAt ℝ (polynomialProfile d q t epsilon) r := by
    rcases hinner with hi | ho
    · exact (polynomialProfile_hasDerivAt_inner q t epsilon r he hi).differentiableAt
    · exact (polynomialProfile_hasDerivAt_outer q t epsilon r he ho).differentiableAt
  have hrad := Sharpness.transverseNorm_hasDerivAt x i hr
  have hψrad : HasDerivAt (fun s : ℝ => polynomialProfile d q t epsilon
      (Sharpness.transverseNorm (x + s • basisVec i)))
      (deriv (polynomialProfile d q t epsilon) r *
        (if i = 0 then 0 else x i / r)) 0 := by
    have hψ : HasDerivAt (polynomialProfile d q t epsilon)
        (deriv (polynomialProfile d q t epsilon) r)
        (Sharpness.transverseNorm (x + (0 : ℝ) • basisVec i)) := by
      simpa [r] using hψdiff.hasDerivAt
    have hcomp := hψ.comp 0 hrad
    simpa [Function.comp_def, r] using hcomp
  have hcoord := Sharpness.axialCoordinatePath_hasDerivAt x i
  have hcoord0 : HasDerivAt (fun s : ℝ => (x + s • basisVec i) 0)
      (if i = 0 then 1 else 0) 0 := by
    simpa using hcoord
  have hcoordSq := hcoord0.pow 2
  have hpath : HasDerivAt
      (fun s : ℝ => polynomialSolution d q t epsilon (x + s • basisVec i))
      (if i = 0 then 2 * x 0 else
        -deriv (polynomialProfile d q t epsilon) r * (x i / r)) 0 := by
    have hbase : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    have hsum := hbase.add (hcoordSq.sub hψrad)
    have hformula :
        (if i = 0 then (2 * x 0) * 1 - 0 else
          (0 : ℝ) - deriv (polynomialProfile d q t epsilon) r * (x i / r)) =
        (if i = 0 then 2 * x 0 else
          -deriv (polynomialProfile d q t epsilon) r * (x i / r)) := by
      split_ifs <;> ring
    convert hsum using 1
    · funext s
      simp [polynomialSolution]
      ring
    · by_cases hi : i = 0 <;> simp [hi, basisVec]
  have hsolDiff : DifferentiableAt ℝ (polynomialSolution d q t epsilon) x := by
    change DifferentiableAt ℝ
      (fun y : Vec d => 1 + (y 0) ^ 2 -
        polynomialProfile d q t epsilon (Sharpness.transverseNorm y)) x
    have hrDiff := (Sharpness.transverseNorm_contDiffAt x hr).differentiableAt (by simp)
    have hconst : DifferentiableAt ℝ (fun _ : Vec d => (1 : ℝ)) x := by fun_prop
    have hcoord : DifferentiableAt ℝ (fun y : Vec d => (y 0) ^ 2) x := by fun_prop
    convert hconst.add (hcoord.sub (hψdiff.comp x hrDiff)) using 1
    funext y
    simp
    ring
  rw [smoothGrad, Sharpness.fderiv_apply_eq_deriv_line hsolDiff i]
  simpa [Function.comp_def, r] using hpath.deriv

end

end CoarseDeGiorgi.SharpnessExamples
