module

public import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationTransverseLipschitz
public import CoarseDeGiorgi.SharpnessExamples.CylinderAxial
public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxCalculus

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem polynomialParallel_eq_perpendicular_scale {d : ℕ}
    (q t epsilon : ℝ) (he : 0 < epsilon) :
    polynomialParallel d q t epsilon =
      ((d : ℝ) - 1) * polynomialPerpendicular d q t epsilon / epsilon ^ 2 := by
  unfold polynomialParallel polynomialPerpendicular
  have hp := Real.rpow_sub he (2 * polynomialHatT d q t) 2
  have hp' : Real.rpow epsilon (2 * polynomialHatT d q t - 2) =
      Real.rpow epsilon (2 * polynomialHatT d q t) / epsilon ^ 2 := by
    simpa only [Real.rpow_eq_pow, Real.rpow_two] using hp
  calc
    ((d : ℝ) - 1) * Real.rpow epsilon (2 * polynomialHatT d q t - 2) =
        ((d : ℝ) - 1) *
          (Real.rpow epsilon (2 * polynomialHatT d q t) / epsilon ^ 2) := by rw [hp']
    _ = _ := by ring

/-- The scalar transverse flux factor has the derivative appropriate to each
smooth side of the coefficient interface. -/
theorem polynomialTransverseFactor_hasDerivAt_inner {d : ℕ}
    {q t epsilon r : ℝ} (hinner : r < 2 * epsilon) :
    HasDerivAt (polynomialTransverseFactor d q t epsilon) 0 r := by
  have hlocal : polynomialTransverseFactor d q t epsilon =ᶠ[𝓝 r]
      fun _ => 2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2 := by
    filter_upwards [Iio_mem_nhds hinner] with s hs
    change s < 2 * epsilon at hs
    simp [polynomialTransverseFactor, hs]
  exact (hasDerivAt_const r (2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2)).congr_of_eventuallyEq hlocal

theorem polynomialTransverseFactor_hasDerivAt_outer {d : ℕ}
    (hd : 3 ≤ d) {q t epsilon r : ℝ} (he : 0 < epsilon) (hr : 0 < r)
    (houter : 2 * epsilon < r) :
    HasDerivAt (polynomialTransverseFactor d q t epsilon)
      ((2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2 - (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)) *
          ((1 - (d : ℝ)) * Real.rpow r (-(d : ℝ)))) r := by
  have hlocal : polynomialTransverseFactor d q t epsilon =ᶠ[𝓝 r]
      fun s => polynomialOuterQ d q t epsilon s := by
    filter_upwards [Ioi_mem_nhds houter] with s hs
    change 2 * epsilon < s at hs
    have hspos : 0 < s := by linarith [he]
    change (if s < 2 * epsilon then
      2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2 else
      polynomialOuterDerivative d q t epsilon s / s) = polynomialOuterQ d q t epsilon s
    rw [ite_eq_right (not_lt_of_ge hs.le)]
    exact polynomialOuterDerivative_div_eq_outerQ hd q t epsilon s hspos
  exact (polynomialOuterQ_hasDerivAt hd q t epsilon r hr).congr_of_eventuallyEq hlocal

/-- The explicit vector flux has the stated coordinate line derivatives away
from the transverse axis and the interface. -/
theorem polynomialFlux_coordinate_lineDeriv {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ} (he : 0 < epsilon) {x : Vec d}
    (hr : 0 < Sharpness.transverseNorm x)
    (hbranch : Sharpness.transverseNorm x < 2 * epsilon ∨
      2 * epsilon < Sharpness.transverseNorm x) (i : Fin d) :
    lineDeriv ℝ (fun y => polynomialFlux d q t epsilon y i) x (basisVec i) =
      if i = 0 then
        2 * polynomialAxialFactor d q t epsilon (Sharpness.transverseNorm x)
      else
        -(polynomialTransverseFactor d q t epsilon (Sharpness.transverseNorm x) +
          deriv (polynomialTransverseFactor d q t epsilon)
            (Sharpness.transverseNorm x) * x i ^ 2 / Sharpness.transverseNorm x) := by
  by_cases hi : i = 0
  · subst i
    have hpath := Sharpness.axialCoordinatePath_hasDerivAt x (0 : Fin d)
    let b := polynomialAxialFactor d q t epsilon (Sharpness.transverseNorm x)
    have hmain : HasDerivAt
        (fun s : ℝ => 2 * (x + s • basisVec (0 : Fin d)) 0 * b) (2 * b) 0 := by
      convert (hpath.const_mul 2).mul (hasDerivAt_const (0 : ℝ) b) using 1
      simp [basisVec]
    have heq : (fun s : ℝ => polynomialFlux d q t epsilon
        (x + s • basisVec (0 : Fin d)) 0) =
        fun s => 2 * (x + s • basisVec (0 : Fin d)) 0 * b := by
      funext s
      simp [polynomialFlux, polynomialAxialFactor, b,
        transverseNorm_add_axial]
    have hline : HasLineDerivAt ℝ
        (fun y => polynomialFlux d q t epsilon y 0) (2 * b) x
          (basisVec (0 : Fin d)) := by
      change HasDerivAt
        (fun s : ℝ => polynomialFlux d q t epsilon
          (x + s • basisVec (0 : Fin d)) 0) (2 * b) 0
      rw [heq]
      exact hmain
    simpa [b] using hline.lineDeriv
  · have hq : HasDerivAt (polynomialTransverseFactor d q t epsilon)
        (deriv (polynomialTransverseFactor d q t epsilon)
          (Sharpness.transverseNorm x)) (Sharpness.transverseNorm x) := by
      rcases hbranch with hinner | houter
      · exact (polynomialTransverseFactor_hasDerivAt_inner hinner).differentiableAt.hasDerivAt
      · exact (polynomialTransverseFactor_hasDerivAt_outer (d := d) hd
          (q := q) (t := t) (epsilon := epsilon) (r := Sharpness.transverseNorm x)
          he hr houter).differentiableAt.hasDerivAt
    have hq0 : HasDerivAt (polynomialTransverseFactor d q t epsilon)
        (deriv (polynomialTransverseFactor d q t epsilon)
          (Sharpness.transverseNorm (x - (0 : Vec d))))
        (Sharpness.transverseNorm (x - (0 : Vec d))) := by
      simpa using hq
    have hP : HasDerivAt (fun s : ℝ => -polynomialTransverseFactor d q t epsilon s)
        (-(deriv (polynomialTransverseFactor d q t epsilon)
          (Sharpness.transverseNorm x)))
        (Sharpness.transverseNorm (x - (0 : Vec d))) := by
      have hneg := (hasDerivAt_id (polynomialTransverseFactor d q t epsilon
        (Sharpness.transverseNorm x))).neg
      have hcomp := hneg.comp (Sharpness.transverseNorm x) hq
      change HasDerivAt (fun s : ℝ => -polynomialTransverseFactor d q t epsilon s)
        (-1 * deriv (polynomialTransverseFactor d q t epsilon)
          (Sharpness.transverseNorm x)) (Sharpness.transverseNorm x) at hcomp
      simpa [sub_zero] using hcomp
    have hr0 : 0 < Sharpness.transverseNorm (x - (0 : Vec d)) := by simpa using hr
    have hrad := radial_coordinate_flux_hasLineDerivAt
      (X := fun _ : ℝ => (1 : ℝ))
      (P := fun s => -polynomialTransverseFactor d q t epsilon s)
      (X' := 0) (P' := -(deriv (polynomialTransverseFactor d q t epsilon)
        (Sharpness.transverseNorm x)))
      (c := (0 : Vec d)) (x := x) (i := i) hi hr0
      (hasDerivAt_const _ _) hP
    have heq : (fun y : Vec d => polynomialFlux d q t epsilon y i) =
        fun y => (1 : ℝ) *
          (-polynomialTransverseFactor d q t epsilon (Sharpness.transverseNorm y)) * y i := by
      funext y
      simp [polynomialFlux, hi]
    rw [heq]
    convert hrad.lineDeriv using 1 <;> simp [hi, div_eq_mul_inv, mul_assoc]
    ring

/-- The divergence of the explicit flux is zero in both open regions. -/
theorem polynomialFlux_divergence_zero {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ} (he : 0 < epsilon) {x : Vec d}
    (hr : 0 < Sharpness.transverseNorm x)
    (hbranch : Sharpness.transverseNorm x < 2 * epsilon ∨
      2 * epsilon < Sharpness.transverseNorm x) :
    ∑ i : Fin d, lineDeriv ℝ (fun y => polynomialFlux d q t epsilon y i) x
      (basisVec i) = 0 := by
  let r := Sharpness.transverseNorm x
  let Q := polynomialTransverseFactor d q t epsilon r
  let Q' := deriv (polynomialTransverseFactor d q t epsilon) r
  let b := polynomialAxialFactor d q t epsilon r
  have hsq : (∑ i : Fin d, if i = 0 then (0 : ℝ) else x i ^ 2) = r ^ 2 := by
    dsimp [r]
    rw [Sharpness.transverseNorm, euclideanNorm_sq]
    unfold vecNormSq vecDot Sharpness.transversePart
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0
    · subst i
      simp
    · simp [hi, pow_two]
  have hcount : (∑ i : Fin d, if i = 0 then (0 : ℝ) else 1) =
      (d : ℝ) - 1 := by
    have heq : (∑ i : Fin d, if i = 0 then (0 : ℝ) else 1) =
        (∑ _i : Fin d, (1 : ℝ)) -
          (∑ i : Fin d, if i = 0 then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> norm_num
    rw [heq]
    simp
  have hterm (i : Fin d) :
      lineDeriv ℝ (fun y => polynomialFlux d q t epsilon y i) x (basisVec i) =
        (if i = 0 then 2 * b else 0) +
          (if i = 0 then 0 else -Q) +
          (if i = 0 then 0 else -(Q' * x i ^ 2 / r)) := by
    by_cases hi : i = 0
    · subst i
      rw [polynomialFlux_coordinate_lineDeriv hd he hr hbranch]
      simp [b, r]
    · rw [polynomialFlux_coordinate_lineDeriv hd he hr hbranch]
      simp [hi, Q, Q', r, pow_two]
      ring
  have hsum1 : (∑ i : Fin d, if i = 0 then 2 * b else 0) = 2 * b := by simp
  have hsum2 : (∑ i : Fin d, if i = 0 then 0 else -Q) = -((d : ℝ) - 1) * Q := by
    calc
      _ = ∑ i : Fin d, (-Q) * (if i = 0 then (0 : ℝ) else 1) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = 0 <;> simp [hi]
      _ = -Q * (∑ i : Fin d, if i = 0 then (0 : ℝ) else 1) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [hcount]; ring
  have hsum3 : (∑ i : Fin d, if i = 0 then 0 else -(Q' * x i ^ 2 / r)) = -r * Q' := by
    calc
      _ = ∑ i : Fin d, (-(Q' / r)) * (if i = 0 then (0 : ℝ) else x i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = 0 <;> simp [hi]
        ring
      _ = -(Q' / r) * (∑ i : Fin d, if i = 0 then (0 : ℝ) else x i ^ 2) := by
        rw [Finset.mul_sum]
      _ = _ := by
        rw [hsq]
        field_simp [ne_of_gt hr]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsum1, hsum2, hsum3]
  change 2 * b + -((d : ℝ) - 1) * Q + -r * Q' = 0
  rcases hbranch with hi | ho
  · have hscale := polynomialParallel_eq_perpendicular_scale (d := d) q t epsilon he
    have hb : b = polynomialParallel d q t epsilon := by
      dsimp [b, r]
      simp [polynomialAxialFactor, hi]
    have hQ : Q = 2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2 := by
      dsimp [Q, r]
      simp [polynomialTransverseFactor, hi]
    have hQ' : Q' = 0 := by
      dsimp [Q', r]
      exact (polynomialTransverseFactor_hasDerivAt_inner hi).deriv
    rw [hb, hQ, hQ']
    rw [hscale]
    ring
  · have hQ : Q = polynomialOuterQ d q t epsilon r := by
        have hrpos : 0 < Sharpness.transverseNorm x := hr
        calc
          Q = polynomialOuterDerivative d q t epsilon r / r := by
            dsimp [Q, r]
            simp [polynomialTransverseFactor, not_lt_of_gt ho]
          _ = polynomialOuterQ d q t epsilon r := by
            dsimp [r]
            exact polynomialOuterDerivative_div_eq_outerQ hd q t epsilon _ hrpos
    have hQouter := polynomialOuterQ_hasDerivAt hd q t epsilon r hr
    have hQtrans := polynomialTransverseFactor_hasDerivAt_outer (d := d) hd
      (q := q) (t := t) (epsilon := epsilon) (r := r) he hr ho
    have hQderiv' : Q' = deriv (polynomialOuterQ d q t epsilon) r := by
      dsimp [Q', r]
      rw [hQtrans.deriv, hQouter.deriv]
    have hb : b = 1 := by
      dsimp [b, r]
      simp [polynomialAxialFactor, not_lt_of_gt ho]
    have hcancel : ((d : ℝ) - 1) * polynomialOuterQ d q t epsilon r +
        r * deriv (polynomialOuterQ d q t epsilon) r = 2 := by
      let C := 2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
        epsilon ^ 2 - (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)
      have hdne : (d : ℝ) - 1 ≠ 0 := by
        have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      have hshift : r * Real.rpow r (-(d : ℝ)) = Real.rpow r (1 - (d : ℝ)) := by
        calc
          r * Real.rpow r (-(d : ℝ)) = Real.rpow r 1 * Real.rpow r (-(d : ℝ)) := by
            congr 1
            exact (Real.rpow_one r).symm
          _ = Real.rpow r (1 + (-(d : ℝ))) :=
            (Real.rpow_add (by dsimp [r]; linarith [hr]) _ _).symm
          _ = _ := by congr 1
      have hOvalue : polynomialOuterQ d q t epsilon r =
          2 / ((d : ℝ) - 1) + C * Real.rpow r (1 - (d : ℝ)) := by rfl
      have hB : ((d : ℝ) - 1) * (2 / ((d : ℝ) - 1)) = 2 := by
        field_simp [hdne]
      calc
        _ = ((d : ℝ) - 1) * (2 / ((d : ℝ) - 1)) +
            ((d : ℝ) - 1) * C * Real.rpow r (1 - (d : ℝ)) +
            r * C * ((1 - (d : ℝ)) * Real.rpow r (-(d : ℝ))) := by
              rw [hOvalue, hQouter.deriv]
              ring
        _ = 2 + C * ((d : ℝ) - 1) * Real.rpow r (1 - (d : ℝ)) +
            C * (1 - (d : ℝ)) * (r * Real.rpow r (-(d : ℝ))) := by rw [hB]; ring
        _ = 2 := by rw [hshift]; ring
    rw [hb, hQ, hQderiv']
    linarith [hcancel]

end

end CoarseDeGiorgi.SharpnessExamples
