module

public import CoarseDeGiorgi.SharpnessExamples.ScalarSumDensity

/-! # Value integrability and global L¹ convergence of the cylinder sum -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Weighted Cauchy--Schwarz pointwise, without any boundedness assumption on
the scalar weight. -/
theorem abs_le_sqrt_inv_weight_mul_sqrt {w u e : ℝ} (hw : 0 < w)
    (he : 0 ≤ e) (hu : w * u ^ 2 ≤ e) :
    |u| ≤ Real.sqrt w⁻¹ * Real.sqrt e := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (inv_nonneg.mpr hw.le), Real.sq_sqrt he]
  have h := mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hw.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using h

/-- The inverse weight and the summed weighted density control the total value. -/
theorem scalarSubsolutionSum_integrable {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    IntegrableOn (scalarSubsolutionSum (d := m + 1) ζ) (originCube 1) := by
  let w := scalarSharpnessWeight (d := m + 1) ζ (cylinderRadialConstant (m + 1))
  let e := fun x => w x * (scalarSubsolutionSum ζ x ^ 2 +
    vecNormSq (scalarSubsolutionGradientSum ζ x))
  have hw : ∀ x, 0 < w x := scalarSharpnessWeight_pos (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))
  have he : ∀ x, 0 ≤ e x := fun x => mul_nonneg (hw x).le
    (add_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
  have hiw := (scalarSharpnessWeight_integrable (d := m + 1) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))).2
  have hie := scalarSubsolutionSum_density_integrable hm hζ0 hζ2
  have hib := Weighted.sqrt_mul_sqrt_integrable hiw hie
    (Eventually.of_forall (fun x => (inv_pos.mpr (hw x)).le)) (Eventually.of_forall he)
  apply hib.mono' (scalarSubsolutionSum_aestronglyMeasurable hm hζ0 hζ2)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  exact abs_le_sqrt_inv_weight_mul_sqrt (hw x) (he x)
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (vecNormSq_nonneg _)) (hw x).le)

/-- The partial values converge in global L¹, hence also in the value part of
the squared-mean-plus-energy completion. -/
theorem scalarSubsolutionSum_tendsto_l1 {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    Tendsto (fun k => eLpNorm
      ((fun x : Vec (m + 1) => ∑ j ∈ Finset.range k, scalarCylinderSubsolution j ζ x) -
        scalarSubsolutionSum ζ) 1 (volume.restrict (originCube 1))) atTop (𝓝 0) := by
  classical
  let μ := volume.restrict (originCube (d := m + 1) 1)
  let f := fun k (x : Vec (m + 1)) => ∑ j ∈ Finset.range k, scalarCylinderSubsolution j ζ x
  let u := scalarSubsolutionSum (d := m + 1) ζ
  have hiu : Integrable u μ := scalarSubsolutionSum_integrable hm hζ0 hζ2
  have hf : ∀ k, AEStronglyMeasurable (f k) μ := by
    intro k
    have h : AEStronglyMeasurable (∑ j ∈ Finset.range k,
        scalarCylinderSubsolution (d := m + 1) j ζ) μ :=
      Finset.aestronglyMeasurable_sum _ (fun j _ =>
        (scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 j).1)
    have heq : (∑ j ∈ Finset.range k, scalarCylinderSubsolution (d := m + 1) j ζ) = f k := by
      funext x
      simp only [Finset.sum_apply, f]
    rwa [heq] at h
  have hb : ∀ k, ∀ x, |f k x - u x| ≤ |u x| := fun k x =>
    (scalarCylinder_partial_error_bounds (by omega) hζ0 hζ2 x k).1
  have hi : ∀ k, Integrable (f k - u) μ := fun k => hiu.abs.mono'
    ((hf k).sub hiu.1) (Eventually.of_forall (fun x => by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hb k x))
  have ht : Tendsto (fun k => ∫ x, |f k x - u x| ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) (fun x => |u x|)
      (fun k => ((hf k).sub hiu.1).norm) hiu.abs
      (fun k => Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs, abs_abs, Pi.sub_apply] using hb k x))
      (Eventually.of_forall (fun x => ?_))
    · simpa only [integral_zero, Real.norm_eq_abs, Pi.sub_apply] using h
    · apply tendsto_const_nhds.congr'
      filter_upwards [scalarCylinder_partials_eventually_eq (by omega) hζ0 hζ2 x] with k hk
      simp only [Pi.sub_apply, f, u, hk.1, sub_self, norm_zero]
  have hconv := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  change Tendsto (fun k => eLpNorm (f k - u) 1 μ) atTop (𝓝 0)
  simp_rw [Weighted.l1_eq_ofReal_integral_abs (hi _)]
  simpa only [Function.comp_def, Pi.sub_apply, ENNReal.ofReal_zero] using hconv

end

end CoarseDeGiorgi.SharpnessExamples
