module

public import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationRadial
public import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationMembership
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

open Homogenization MeasureTheory Set
open Topology

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

def polynomialOuterQ (d : ℕ) (q t epsilon r : ℝ) : ℝ :=
  2 / ((d : ℝ) - 1) +
    (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
        epsilon ^ 2 -
      (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)) *
      Real.rpow r (1 - (d : ℝ))

theorem polynomialOuterDerivative_div_eq_outerQ {d : ℕ}
    (hd : 3 ≤ d) (q t epsilon r : ℝ) (hr : 0 < r) :
    polynomialOuterDerivative d q t epsilon r / r =
      polynomialOuterQ d q t epsilon r := by
  have hD := polynomialOuterDerivative_eq_linear_rpow hd q t epsilon r hr
  have hshift : r * Real.rpow r (1 - (d : ℝ)) =
      Real.rpow r (2 - (d : ℝ)) := by
    calc
      r * Real.rpow r (1 - (d : ℝ)) =
          Real.rpow r 1 * Real.rpow r (1 - (d : ℝ)) := by
            congr 1
            exact (Real.rpow_one r).symm
      _ = Real.rpow r (1 + (1 - (d : ℝ))) := (Real.rpow_add hr _ _).symm
      _ = _ := by congr 1; ring_nf
  have hshift' : r * r ^ (1 - (d : ℝ)) = r ^ (2 - (d : ℝ)) := by
    simpa only [Real.rpow_eq_pow] using hshift
  have hquot : r ^ (2 - (d : ℝ)) / r =
      r ^ (1 - (d : ℝ)) := by
    calc
      r ^ (2 - (d : ℝ)) / r =
          (r * r ^ (1 - (d : ℝ))) / r := by
            simpa only [Real.rpow_eq_pow] using
              congrArg (fun z : ℝ => z / r) hshift.symm
      _ = r ^ (1 - (d : ℝ)) := by field_simp [ne_of_gt hr]
  rw [hD]
  dsimp [polynomialOuterQ]
  field_simp [ne_of_gt hr]
  rw [← hshift']
  ring

theorem polynomialOuterQ_hasDerivAt {d : ℕ} (_hd : 3 ≤ d)
    (q t epsilon r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s => polynomialOuterQ d q t epsilon s)
      ((2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2 -
        (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)) *
        ((1 - (d : ℝ)) * Real.rpow r (-(d : ℝ)))) r := by
  let C := 2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
      epsilon ^ 2 - (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)
  have hp : HasDerivAt (fun z : ℝ => Real.rpow z (1 - (d : ℝ)))
      ((1 - (d : ℝ)) * Real.rpow r (-(d : ℝ))) r := by
    change HasDerivAt (fun z : ℝ => z ^ (1 - (d : ℝ)))
      ((1 - (d : ℝ)) * r ^ (-(d : ℝ))) r
    convert Real.hasDerivAt_rpow_const (x := r) (p := 1 - (d : ℝ))
      (Or.inl hr.ne') using 1
    congr 1
    ring_nf
  have h := (hasDerivAt_const r (2 / ((d : ℝ) - 1))).add
    ((hasDerivAt_const r C).mul hp)
  convert h using 1
  · funext z
    simp [polynomialOuterQ, C]
  · simp only [zero_add, zero_mul]
    rfl

/-- The matched transverse scalar flux coefficient is Lipschitz on bounded
nonnegative radial intervals. -/
theorem polynomialTransverseFactor_lipschitzOn {d : ℕ} (hd : 3 ≤ d)
    (q t epsilon S : ℝ) (he : 0 < epsilon) (hR : 2 * epsilon ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (0 : ℝ) S, ∀ y ∈ Icc (0 : ℝ) S,
      |polynomialTransverseFactor d q t epsilon x -
        polynomialTransverseFactor d q t epsilon y| ≤ K * |x - y| := by
  let R := 2 * epsilon
  let f : ℝ → ℝ := fun r => polynomialOuterQ d q t epsilon r
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRS : R ≤ S := by simpa [R] using hR
  have hderivCont : ContinuousOn (fun r => deriv f r) (Icc R S) := by
    intro r hr
    have hrpos : 0 < r := hRpos.trans_le hr.1
    have heq : (fun z => deriv f z) =ᶠ[𝓝[Icc R S] r]
        (fun z => (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2 - (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)) *
          ((1 - (d : ℝ)) * Real.rpow z (-(d : ℝ)))) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hrpos)] with z hz
      exact (polynomialOuterQ_hasDerivAt hd q t epsilon z hz).deriv
    have hvalue : deriv f r =
        (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2 - (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)) *
          ((1 - (d : ℝ)) * Real.rpow r (-(d : ℝ))) := by
      exact (polynomialOuterQ_hasDerivAt hd q t epsilon r hrpos).deriv
    have hpow : ContinuousAt (fun z : ℝ => Real.rpow z (-(d : ℝ))) r :=
      Real.continuousAt_rpow_const r _ (Or.inl hrpos.ne')
    have hcont : ContinuousWithinAt (fun z =>
        (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
        epsilon ^ 2 - (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)) *
        ((1 - (d : ℝ)) * Real.rpow z (-(d : ℝ)))) (Icc R S) r := by
      exact (((hpow.const_mul (1 - (d : ℝ))).const_mul
        (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2 - (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1))).continuousWithinAt)
    exact (heq.congr_continuousWithinAt hvalue).2 (by simpa [f] using hcont)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hderivCont
  let K : ℝ := max 0 M
  have hK : 0 ≤ K := le_max_left _ _
  have hderivBound : ∀ r ∈ Icc R S, ‖deriv f r‖ ≤ K := by
    intro r hr
    exact (hM r hr).trans (le_max_right _ _)
  have hfDiff : ∀ r ∈ Icc R S, DifferentiableAt ℝ f r := by
    intro r hr
    have hrpos : 0 < r := hRpos.trans_le hr.1
    exact (polynomialOuterQ_hasDerivAt hd q t epsilon r hrpos).differentiableAt
  have hfLip {x y : ℝ} (hx : x ∈ Icc R S) (hy : y ∈ Icc R S) :
      |f y - f x| ≤ K * |y - x| := by
    have h := (convex_Icc R S).norm_image_sub_le_of_norm_deriv_le hfDiff hderivBound hx hy
    simpa only [Real.norm_eq_abs] using h
  have hmatch : f R = 2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2 := by
    have h := polynomialOuterDerivative_div_eq_outerQ hd q t epsilon R hRpos
    have hi := polynomialTransverseFactor_interface (d := d) hd
      (q := q) (t := t) (epsilon := epsilon) he
    dsimp [f, R] at h
    rw [h] at hi
    exact hi
  refine ⟨K, hK, ?_⟩
  intro x hx y hy
  have hxs := hx.2
  have hys := hy.2
  by_cases hxR : x < R <;> by_cases hyR : y < R
  · simp [polynomialTransverseFactor, R, hxR, hyR]
    positivity
  · have hyR' : y ∈ Icc R S := ⟨le_of_not_gt hyR, hys⟩
    have hxInner : polynomialTransverseFactor d q t epsilon x =
        2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2 := by
      simp [polynomialTransverseFactor, R, hxR]
    have hyMatch : polynomialTransverseFactor d q t epsilon y = f y := by
      simpa [polynomialTransverseFactor, R, not_lt_of_ge hyR'.1] using
        polynomialOuterDerivative_div_eq_outerQ hd q t epsilon y (lt_of_lt_of_le hRpos hyR'.1)
    rw [hxInner, hyMatch, ← hmatch]
    have hRf : R ∈ Icc R S := ⟨le_rfl, hRS⟩
    have hfy := hfLip (x := R) (y := y) hRf hyR'
    calc
      |f R - f y| = |f y - f R| := abs_sub_comm _ _
      _ ≤ K * |y - R| := hfy
      _ ≤ K * |x - y| := by
        apply mul_le_mul_of_nonneg_left _ hK
        have hxy : x ≤ y := (le_of_lt hxR).trans (le_of_not_gt hyR)
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hyR))]
        rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        linarith
  · have hxR' : x ∈ Icc R S := ⟨le_of_not_gt hxR, hxs⟩
    have hyInner : polynomialTransverseFactor d q t epsilon y =
        2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2 := by
      simp [polynomialTransverseFactor, R, hyR]
    have hxMatch : polynomialTransverseFactor d q t epsilon x = f x := by
      simpa [polynomialTransverseFactor, R, not_lt_of_ge hxR'.1] using
        polynomialOuterDerivative_div_eq_outerQ hd q t epsilon x (lt_of_lt_of_le hRpos hxR'.1)
    rw [hxMatch, hyInner, ← hmatch]
    have hRf : R ∈ Icc R S := ⟨le_rfl, hRS⟩
    have hfx := hfLip (x := R) (y := x) hRf hxR'
    calc
      |f x - f R| ≤ K * |x - R| := hfx
      _ ≤ K * |x - y| := by
        apply mul_le_mul_of_nonneg_left _ hK
        rw [abs_of_nonneg (sub_nonneg.mpr hxR'.1)]
        have hyx : y ≤ x := (le_of_lt hyR).trans hxR'.1
        rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        linarith
  · have hxR' : x ∈ Icc R S := ⟨le_of_not_gt hxR, hxs⟩
    have hyR' : y ∈ Icc R S := ⟨le_of_not_gt hyR, hys⟩
    have hxmatch : polynomialTransverseFactor d q t epsilon x = f x := by
      simpa [polynomialTransverseFactor, R, not_lt_of_ge hxR'.1] using
        polynomialOuterDerivative_div_eq_outerQ hd q t epsilon x (lt_of_lt_of_le hRpos hxR'.1)
    have hymatch : polynomialTransverseFactor d q t epsilon y = f y := by
      simpa [polynomialTransverseFactor, R, not_lt_of_ge hyR'.1] using
        polynomialOuterDerivative_div_eq_outerQ hd q t epsilon y (lt_of_lt_of_le hRpos hyR'.1)
    rw [hxmatch, hymatch]
    simpa [abs_sub_comm] using hfLip (x := x) (y := y) hxR' hyR'
end

end CoarseDeGiorgi.SharpnessExamples
