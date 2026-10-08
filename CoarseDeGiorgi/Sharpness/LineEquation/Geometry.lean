import CoarseDeGiorgi.Sharpness.Defs
import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Homogenization

namespace CoarseDeGiorgi.Sharpness

private theorem vecNormSq_add_eq {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  unfold vecNormSq vecDot
  calc
    (∑ i, (x i + y i) * (x i + y i)) =
        ∑ i, (x i * x i + 2 * (x i * y i) + y i * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, x i * x i) + 2 * (∑ i, x i * y i) + (∑ i, y i * y i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

private theorem transversePart_add_basis {d : ℕ} [NeZero d]
    (x : Vec d) (i : Fin d) (hi : i ≠ 0) (t : ℝ) :
    transversePart (x + t • basisVec i) = transversePart x + t • basisVec i := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [transversePart, basisVec, hi]
  · have hjval : j.val ≠ 0 := by
      intro h
      exact hj (Fin.ext h)
    simp [transversePart, hjval, basisVec]

private theorem transversePart_add_basis_zero {d : ℕ} [NeZero d]
    (x : Vec d) (t : ℝ) :
    transversePart (x + t • basisVec (0 : Fin d)) = transversePart x := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [transversePart]
  · have hjval : j.val ≠ 0 := by
      intro h
      exact hj (Fin.ext h)
    simp [transversePart, hjval, basisVec, hj]

/-- The transverse distance has coordinate derivative `yᵢ / |y|` away from the
singular axis; its derivative in the axial direction is zero. -/
lemma transverseNorm_hasDerivAt {d : ℕ} [NeZero d]
    (x : Vec d) (i : Fin d) (hr : 0 < transverseNorm x) :
    HasDerivAt (fun t : ℝ => transverseNorm (x + t • basisVec i))
      (if i = 0 then (0 : ℝ) else x i / transverseNorm x) (0 : ℝ) := by
  let q : ℝ → ℝ := fun t => vecNormSq (transversePart (x + t • basisVec i))
  have hq0 : q 0 = transverseNorm x ^ 2 := by
    dsimp [q]
    simp only [zero_smul, add_zero]
    change vecNormSq (transversePart x) = euclideanNorm (transversePart x) ^ 2
    exact (euclideanNorm_sq _).symm
  have hroot : Real.sqrt (q 0) = transverseNorm x := by
    rw [hq0, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  by_cases hi : i = 0
  · subst i
    have hqconst : q = fun _ => q 0 := by
      funext t
      dsimp [q]
      rw [transversePart_add_basis_zero]
      simp
    have hq : HasDerivAt q 0 0 := by
      rw [hqconst]
      exact hasDerivAt_const 0 (q 0)
    have hroot' := (Real.hasDerivAt_sqrt (ne_of_gt (by rw [hq0]; positivity))).comp 0 hq
    have hroot'' : HasDerivAt (fun t : ℝ => Real.sqrt (q t))
        (1 / (2 * Real.sqrt (q 0)) * 0) 0 := by
      convert hroot' using 1; rfl
    change HasDerivAt (fun t : ℝ => Real.sqrt (q t)) 0 0
    simpa [hroot] using hroot''
  · have hpart := transversePart_add_basis x i hi
    have hqformula : ∀ t, q t = q 0 + 2 * t * x i + t ^ 2 := by
      intro t
      dsimp [q]
      rw [hpart t, vecNormSq_add_eq, vecNormSq_smul, vecNormSq_basisVec]
      have hdot : vecDot (transversePart x) (basisVec i) = x i := by
        rw [vecDot_basisVec_right]
        simp [transversePart, hi]
      have hdotScale : vecDot (transversePart x) (t • basisVec i) =
          t * vecDot (transversePart x) (basisVec i) := by
        unfold vecDot
        simp only [Pi.smul_apply, smul_eq_mul]
        calc
          (∑ j, transversePart x j * (t * basisVec i j)) =
              ∑ j, t * (transversePart x j * basisVec i j) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = t * ∑ j, transversePart x j * basisVec i j := by rw [Finset.mul_sum]
      rw [hdotScale, hdot]
      simp
      ring
    have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    have hlin : HasDerivAt (fun t : ℝ => 2 * t * x i) (2 * x i) 0 := by
      simpa using (hid.const_mul 2).mul_const (x i)
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    have hq' : HasDerivAt (fun t : ℝ => q 0 + 2 * t * x i + t ^ 2)
        (2 * x i) 0 := by
      have hc : HasDerivAt (fun _ : ℝ => q 0) 0 0 := hasDerivAt_const 0 (q 0)
      have hadd : HasDerivAt
          ((fun _ : ℝ => q 0) + (fun t : ℝ => 2 * t * x i) + (fun t : ℝ => t ^ 2))
          (2 * x i) 0 := by
        simpa using hc.add hlin |>.add hsq
      have hfun :
          ((fun _ : ℝ => q 0) + (fun t : ℝ => 2 * t * x i) + (fun t : ℝ => t ^ 2)) =
            (fun t : ℝ => q 0 + 2 * t * x i + t ^ 2) := by
        funext t
        rfl
      rw [hfun] at hadd
      exact hadd
    have hq : HasDerivAt q (2 * x i) 0 := by
      rw [show q = (fun t => q 0 + 2 * t * x i + t ^ 2) from funext hqformula]
      exact hq'
    have hqpos : 0 < q 0 := by
      rw [hq0]
      positivity
    have hrootne : Real.sqrt (q 0) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hqpos)
    have hcoeff : (Real.sqrt (q 0))⁻¹ * (2 : ℝ)⁻¹ * (2 * x i) =
        1 / (2 * Real.sqrt (q 0)) * (2 * x i) := by
      field_simp [hrootne]
    have hroot' := (Real.hasDerivAt_sqrt (ne_of_gt hqpos)).comp 0 hq
    have hderiv : (Real.sqrt (q 0))⁻¹ * (2 : ℝ)⁻¹ * (2 * x i) =
        x i / transverseNorm x := by
      rw [hroot]
      field_simp [hr.ne']
    have hroot'' : HasDerivAt (fun t : ℝ => Real.sqrt (q t))
        ((Real.sqrt (q 0))⁻¹ * (2 : ℝ)⁻¹ * (2 * x i)) 0 := by
      convert hroot' using 1; rfl
    change HasDerivAt (fun t : ℝ => Real.sqrt (q t))
      (if i = 0 then (0 : ℝ) else x i / transverseNorm x) 0
    simpa [hi, hderiv] using hroot''
end CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.Sharpness

/-- The transverse projection is smooth as a map into the ambient coordinate space. -/
lemma transversePart_contDiff {d : ℕ} :
    ContDiff ℝ ⊤ (transversePart (d := d)) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val = 0
  · simpa [transversePart, hi] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec d => (0 : ℝ)))
  · simpa [transversePart, hi] using (contDiff_apply ℝ ℝ i)

/-- The squared transverse radius is smooth, including on the singular axis. -/
lemma transverseNormSq_contDiff {d : ℕ} :
    ContDiff ℝ ⊤ (fun x : Vec d => vecNormSq (transversePart x)) := by
  have hp := transversePart_contDiff (d := d)
  change ContDiff ℝ ⊤ (fun x : Vec d =>
    ∑ i, transversePart x i * transversePart x i)
  fun_prop

end CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.Sharpness

/-- The transverse distance is smooth away from the singular axis. -/
lemma transverseNorm_contDiffAt {d : ℕ} (x : Vec d)
    (hr : 0 < transverseNorm x) : ContDiffAt ℝ ⊤ transverseNorm x := by
  have hq := transverseNormSq_contDiff (d := d)
  have hqpos : 0 < vecNormSq (transversePart x) := by
    have heq : vecNormSq (transversePart x) = transverseNorm x ^ 2 := by
      dsimp [transverseNorm]
      rw [← euclideanNorm_sq]
    rw [heq]
    positivity
  have hsqrt := Real.contDiffAt_sqrt (n := ⊤) (ne_of_gt hqpos)
  change ContDiffAt ℝ ⊤ (fun y : Vec d => Real.sqrt (vecNormSq (transversePart y))) x
  exact hsqrt.comp x hq.contDiffAt

/-- Derivative of the axial coordinate along a coordinate line. -/
lemma axialCoordinatePath_hasDerivAt {d : ℕ} [NeZero d] (x : Vec d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => (x + t • basisVec i) 0)
      (if i = 0 then 1 else 0) 0 := by
  have hcoordFun : (fun t : ℝ => (x + t • basisVec i) 0) =
      (fun t => x 0 + if i = 0 then t else 0) := by
    funext t
    by_cases hi : i = 0
    · subst i
      simp [basisVec]
    · simp [basisVec, hi]
  rw [hcoordFun]
  by_cases hi : i = 0
  · subst i
    have hadd := (hasDerivAt_const (0 : ℝ) (x 0)).add (hasDerivAt_id (0 : ℝ))
    have hadd' : HasDerivAt (fun t : ℝ => x 0 + t) (1 : ℝ) 0 := by
      convert hadd using 1
      · funext t
        rfl
      · ring
    simpa using hadd'
  · have hconst : HasDerivAt (fun _ : ℝ => x 0) 0 0 :=
      hasDerivAt_const (0 : ℝ) (x 0)
    simpa [hi] using hconst

/-- The Fréchet derivative on a coordinate vector is the derivative along the
corresponding affine coordinate line. -/
lemma fderiv_apply_eq_deriv_line {d : ℕ} {f : Vec d → ℝ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) (i : Fin d) :
    fderiv ℝ f x (basisVec i) = deriv (fun t : ℝ => f (x + t • basisVec i)) 0 := by
  let path : ℝ → Vec d := fun t => x + t • basisVec i
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have hscale : HasDerivAt (fun t : ℝ => t • basisVec i) (basisVec i) 0 := by
    simpa using hid.smul_const (basisVec i)
  have hconst : HasDerivAt (fun _ : ℝ => x) 0 0 := hasDerivAt_const 0 x
  have hadd := hconst.add hscale
  have hfun : ((fun _ : ℝ => x) + fun t : ℝ => t • basisVec i) = path := by
    funext t
    rfl
  rw [hfun] at hadd
  have hpath : HasDerivAt path (basisVec i) 0 := by simpa using hadd
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp [path])
  calc
    fderiv ℝ f x (basisVec i) = deriv (f ∘ path) 0 := hcomp.deriv.symm
    _ = deriv (fun t : ℝ => f (x + t • basisVec i)) 0 := rfl

end CoarseDeGiorgi.Sharpness
