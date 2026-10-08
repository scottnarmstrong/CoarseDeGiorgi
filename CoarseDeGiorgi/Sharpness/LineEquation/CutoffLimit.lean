module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import CoarseDeGiorgi.Statements.SmoothGrad
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

open Homogenization MeasureTheory Filter Set
open scoped Topology BigOperators

namespace CoarseDeGiorgi.Sharpness

/-- Pairing a compact C¹ test with an L¹ field is integrable. -/
lemma integrable_smoothGrad_dot {d : ℕ} {V : Set (Vec d)}
    (φ : Vec d → ℝ) (F : Vec d → Vec d)
    (hφ : ContDiff ℝ (1 : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hF : ∀ i, IntegrableOn (fun x => F x i) V) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (F x)) V := by
  apply integrable_finsetSum
  intro i hi
  have hd : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support
    (hc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  exact (hF i).bdd_mul hd.aestronglyMeasurable (Eventually.of_forall hC)

/-- Pointwise gradient product rule in the coordinate representation of `smoothGrad`. -/
lemma smoothGrad_mul {d : ℕ} {f g : Vec d → ℝ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    smoothGrad (fun y => f y * g y) x =
      f x • smoothGrad g x + g x • smoothGrad f x := by
  funext i
  unfold smoothGrad
  change fderiv ℝ (f * g) x (basisVec i) = _
  rw [fderiv_mul hf hg]
  simp only [add_apply, smul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end CoarseDeGiorgi.Sharpness
