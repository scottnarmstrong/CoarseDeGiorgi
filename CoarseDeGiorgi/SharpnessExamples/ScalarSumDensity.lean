module

public import CoarseDeGiorgi.SharpnessExamples.ScalarSumSupport
public import CoarseDeGiorgi.SharpnessExamples.ScalarEnergyIntegral
public import CoarseDeGiorgi.SharpnessExamples.ScalarSeries
public import CoarseDeGiorgi.Weighted.Truncation.Closure

/-! # An integrable weighted density for the cylinder series -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem scalarCylinderSubsolution_memH1a_explicit {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    MemH1a (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)))
      (originCube 1) (scalarCylinderSubsolution (d := m + 1) n ζ) (scalarCylinderGradient n ζ) :=
  Weighted.MemH1a.congr_ae (scalarCylinderSubsolution_memH1a (d := m + 1) (by omega) hζ0 hζ2 n)
    Filter.EventuallyEq.rfl (ae_restrict_of_ae (scalarCylinderSubsolution_gradient_ae hm hζ0 hζ2 n))

def scalarCylinderDensity {d : ℕ} [NeZero d] (n : ℕ) (ζ : ℝ) (x : Vec d) : ℝ :=
  scalarSharpnessWeight ζ (cylinderRadialConstant d) x *
    (scalarCylinderSubsolution n ζ x ^ 2 + vecNormSq (scalarCylinderGradient n ζ x))

theorem scalarCylinderDensity_nonneg {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) (x : Vec d) :
    0 ≤ scalarCylinderDensity n ζ x :=
  mul_nonneg (scalarSharpnessWeight_pos hd hζ0 hζ2 (cylinderRadialConstant_pos hd) x).le
    (add_nonneg (sq_nonneg _) (vecNormSq_nonneg _))

theorem scalarCylinderDensity_aestronglyMeasurable {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    AEStronglyMeasurable (scalarCylinderDensity (d := m + 1) n ζ)
      (volume.restrict (originCube 1)) := by
  have hu := scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 n
  have hc : Continuous (fun z : Vec (m + 1) => vecNormSq z) := by
    unfold vecNormSq vecDot
    fun_prop
  exact (scalarSharpnessWeight_measurable ζ (cylinderRadialConstant (m + 1))).aestronglyMeasurable.mul
    ((hu.1.pow 2).add (hc.comp_aestronglyMeasurable hu.2.1))

theorem scalarCylinderDensity_integrable {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    IntegrableOn (scalarCylinderDensity (d := m + 1) n ζ) (originCube 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (scalarCylinderDensity_aestronglyMeasurable hm hζ0 hζ2 n)
    (Filter.Eventually.of_forall (scalarCylinderDensity_nonneg (by omega) hζ0 hζ2 n))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (scalarCylinder_value_energy_bound hm hζ0 hζ2 n)

theorem scalarCylinderDensity_summable_integral_norm {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    Summable (fun n => ∫ x in originCube 1,
      ‖scalarCylinderDensity (d := m + 1) n ζ x‖ ∂volume) := by
  have hgeom : Summable (fun n : ℕ =>
      2 * (4 : ℝ) ^ m * scalarEnergyConstant (m + 1) * (1 / 2 : ℝ) ^ (n + 1)) := by
    convert summable_geometric_two.mul_left
      (2 * (4 : ℝ) ^ m * scalarEnergyConstant (m + 1) * (1 / 2 : ℝ)) using 1
    funext n
    rw [pow_succ]
    ring
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ hgeom
  intro n
  have hbound := scalarCylinder_value_energy_bound hm hζ0 hζ2 n
  have hnn := scalarCylinderDensity_nonneg (d := m + 1) (by omega) hζ0 hζ2 n
  have hi := scalarCylinderDensity_integrable hm hζ0 hζ2 n
  change (∫⁻ x in originCube 1, ENNReal.ofReal (scalarCylinderDensity n ζ x) ∂volume) ≤ _ at hbound
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)] at hbound
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (by positivity) (scalarEnergyConstant_nonneg _ (by omega)))
      (by positivity))).mp hbound

theorem scalarSubsolutionSum_aestronglyMeasurable {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    AEStronglyMeasurable (scalarSubsolutionSum (d := m + 1) ζ)
      (volume.restrict (originCube 1)) :=
  AEStronglyMeasurable.tsum (fun n =>
    (scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 n).1)

theorem scalarSubsolutionGradientSum_aestronglyMeasurable {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    AEStronglyMeasurable (scalarSubsolutionGradientSum (d := m + 1) ζ)
      (volume.restrict (originCube 1)) :=
  AEStronglyMeasurable.tsum (fun n =>
    (scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 n).2.1)

/-- The source's disjoint-support series has integrable weighted value and
gradient squares. -/
theorem scalarSubsolutionSum_density_integrable {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    IntegrableOn (fun x : Vec (m + 1) =>
      scalarSharpnessWeight ζ (cylinderRadialConstant (m + 1)) x *
        (scalarSubsolutionSum ζ x ^ 2 + vecNormSq (scalarSubsolutionGradientSum ζ x)))
      (originCube 1) := by
  have hi := integrable_tsum_of_summable_integral_norm
    (scalarCylinderDensity_integrable hm hζ0 hζ2)
    (scalarCylinderDensity_summable_integral_norm hm hζ0 hζ2)
  have heq : (fun x : Vec (m + 1) => ∑' n, scalarCylinderDensity n ζ x) =
      fun x => scalarSharpnessWeight ζ (cylinderRadialConstant (m + 1)) x *
        (scalarSubsolutionSum ζ x ^ 2 + vecNormSq (scalarSubsolutionGradientSum ζ x)) := by
    funext x
    exact scalarCylinder_density_tsum (by omega) hζ0 hζ2 x _
  rwa [heq] at hi

end

end CoarseDeGiorgi.SharpnessExamples
