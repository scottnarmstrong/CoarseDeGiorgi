import CoarseDeGiorgi.Weighted.LowerSpecSup
import Mathlib.Algebra.QuadraticDiscriminant

namespace CoarseDeGiorgi.Weighted.LowerResponseImpl

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Scalar multiples are literal weighted-space pairs. -/
theorem lower_memH1a_smul [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) (c : ℝ) : MemH1a a V (c • w) (c • G) := by
  obtain ⟨f, ht, hL⟩ := hw.smoothGraph_tendsto hV hne ha
  have hi := (memH1a_memW11 hV hne ha hw).1
  let F := memH1aEnergyField hV.isOpen ha hw
  have hLs : Tendsto (fun n => eLpNorm ((c • f n).val - c • w) 1
      (volume.restrict V)) atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul hL (Or.inr (by simp : ‖c‖ₑ ≠ ⊤))
    simpa only [mul_zero, Submodule.coe_smul_of_tower, ← smul_sub,
      eLpNorm_const_smul] using hh
  have hts : Tendsto (fun n => smoothGraphMap hV.isOpen ha (c • f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V (c • w),
        ((c • F : GradientCore ha) : GradientHilbert ha)))) := by
    simpa only [map_smul, ← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul, F,
      volumeAverage_smul, UniformSpace.Completion.coe_smul] using ht.const_smul c
  have hout := memH1a_of_graph_tendsto_and_l1 hV.isOpen ha
    (f := fun n => c • f n) (G := c • F) (hi.smul c) hLs hts
  simpa only [show (c • F).field = c • F.field from rfl,
    F, memH1aEnergyField_field] using hout

/-- Substitute cw into the full supremum, retaining the scalar polynomial. -/
theorem lowerResponseInv_scalar_test [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) (e : Vec d) (c : ℝ) :
    -c ^ 2 * volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x))) +
      2 * c * vecDot e (volumeAverageVec V G) ≤
        vecDot e (matVecMul (lowerResponseInv a V hV hne ha) e) := by
  have hc := lower_memH1a_smul hV hne ha hw c
  have hb : volumeAverage V (fun x =>
      -vecDot ((c • G) x) (matVecMul (a x) ((c • G) x)) +
        2 * vecDot e ((c • G) x)) ≤
      vecDot e (matVecMul (lowerResponseInv a V hV hne ha) e) := by
    rw [lowerResponseInv_riesz]
    exact lower_integrand_le hV hne ha e hc
  have hq : IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) V :=
    GradientCore.quadratic_integrable ha (memH1aEnergyField hV.isOpen ha hw)
  have hcoord := (memH1a_memW11 hV hne ha hw).2.1
  have hd : IntegrableOn (fun x => vecDot e (G x)) V :=
    by simpa only [IntegrableOn, Function.comp_def, lowerDot_apply, memH1aEnergyField_field] using
      (lowerDot e).integrable_comp
        (GradientCore.integrable ha (memH1aEnergyField hV.isOpen ha hw))
  have heq : volumeAverage V (fun x =>
      -vecDot ((c • G) x) (matVecMul (a x) ((c • G) x)) +
        2 * vecDot e ((c • G) x)) =
      -c ^ 2 * volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x))) +
        2 * c * vecDot e (volumeAverageVec V G) := by
    simp only [Pi.smul_apply, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    have hf : (fun x => -(c * (c * vecDot (G x) (matVecMul (a x) (G x)))) +
        2 * (c * vecDot e (G x))) =
        (fun x => (-c ^ 2) * vecDot (G x) (matVecMul (a x) (G x))) +
          (fun x => (2 * c) * vecDot e (G x)) := by funext x; simp only [Pi.add_apply]; ring
    rw [hf, volumeAverage_add (hq.const_mul _) (hd.const_mul _)]
    rw [show (fun x => (-c ^ 2) * vecDot (G x) (matVecMul (a x) (G x))) =
      (-c ^ 2) • (fun x => vecDot (G x) (matVecMul (a x) (G x))) by rfl,
      volumeAverage_smul]
    rw [show (fun x => (2 * c) * vecDot e (G x)) =
      (2 * c) • (fun x => vecDot e (G x)) by rfl,
      volumeAverage_smul, volumeAverage_vecDot_left e G hcoord]
    rfl
  exact heq ▸ hb

/-- Optimization in c, including the zero-energy case, via the discriminant. -/
theorem lower_scalar_optimization {E m Q : ℝ}
    (h : ∀ c : ℝ, -c ^ 2 * E + 2 * c * m ≤ Q) : m ^ 2 ≤ Q * E := by
  have hh : discrim E (-2 * m) Q ≤ 0 :=
    discrim_le_zero (fun c => by have := h c; nlinarith)
  unfold discrim at hh
  nlinarith

/-- Source e.lower.mean.gradient, directional inequality, in every dimension. -/
theorem lowerResponseInv_mean_gradient
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) (e : Vec d) :
    (vecDot e (volumeAverageVec V G)) ^ 2 ≤
      vecDot e (matVecMul (lowerResponseInv a V hV hne ha) e) *
        volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x))) := by
  cases d with
  | zero => simp [vecDot]
  | succ n => exact lower_scalar_optimization (lowerResponseInv_scalar_test hV hne ha hw e)



end CoarseDeGiorgi.Weighted.LowerResponseImpl
