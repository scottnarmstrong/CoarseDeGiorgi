module

public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxTesting
public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxIdentity
public import CoarseDeGiorgi.SharpnessExamples.ScalarSumMembership
public import CoarseDeGiorgi.Weighted.ZeroCore
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution

/-! # Each source cylinder profile is a weighted subsolution -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The source profile satisfies the weak subsolution inequality, including
the matched inner interface and positive outer flux jump. -/
theorem scalarCylinderSubsolution_isWeightedSubsolution {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    IsWeightedSubsolution (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)))
      (originCube 1) (scalarCylinderSubsolution (d := m + 1) n ζ) (scalarCylinderGradient n ζ) := by
  classical
  have hV := Whitney.source_cube_domain (d := m + 1) (by norm_num : (0 : ℝ) < 1)
  have ha := scalarSharpnessCoefficient_isWeightedCoeffOn (d := m + 1) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))
  have hu := scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 n
  refine ⟨hu, ?_⟩
  intro φ hφ hc hs hn
  let μ := volume.restrict (originCube (d := m + 1) 1)
  let a := scalarSharpnessCoefficient (d := m + 1) ζ (cylinderRadialConstant (m + 1))
  let G := scalarCylinderGradient (d := m + 1) n ζ
  let J := fun x : Vec (m + 1) => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))
  let ε := cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))
  let δ := fun k : ℕ => ε / ((k + 2 : ℕ) : ℝ)
  let χ := fun k (x : Vec (m + 1)) => scalarOuterFluxCutoff ε (δ k)
    (transverseNorm (x - cylinderCenter (cylinderB n)))
  have hε : 0 < ε := (cylinderRadius_data (d := m + 1) (n := n) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))).1
  have hδ0 : ∀ k, 0 < δ k := fun k => div_pos hε (by positivity)
  have hδε : ∀ k, δ k < ε := by
    intro k
    apply div_lt_self hε
    exact_mod_cast (by omega : 1 < k + 2)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat ε)
  have hφcore := Weighted.isSmoothCore_of_supported ha hφ hc
  have hiJ : Integrable J μ := (Weighted.pairing_integrable_and_bound ha
    (Weighted.smoothGrad_aestronglyMeasurable hV.isOpen hφ.contDiffOn) hu.2.1
    hφcore.2.2 (Weighted.MemH1a.energy_lt_top hV.isOpen ha hu)).1
  have hχmeas : ∀ k, Measurable (χ k) := by
    intro k
    obtain ⟨K, hK⟩ := scalarOuterFluxCutoff_exists_lipschitz ε (δ k)
    exact (hK.continuous.comp (lineRadius_continuous.comp (continuous_id.sub continuous_const))).measurable
  have hχbounds : ∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1 := fun k x =>
    scalarOuterFluxCutoff_bounds ε (δ k) _
  have hlim : ∀ x, Tendsto (fun k => χ k x * J x) atTop (𝓝 (J x)) := by
    intro x
    let r := transverseNorm (x - cylinderCenter (d := m + 1) (cylinderB n))
    by_cases hr : r < 2 * ε
    · have hgap : 0 < 2 * ε - r := sub_pos.mpr hr
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_order.mp hδlim).2 (2 * ε - r) hgap] with k hk
      have hone : χ k x = 1 := scalarOuterFluxCutoff_eq_one (hδ0 k) (by linarith only [hk])
      simp only [hone, one_mul]
    · have hGzero : G x = 0 := scalarCylinderGradient_eq_zero_outer (by omega) hζ0 hζ2 (le_of_not_gt hr)
      have hJzero : J x = 0 := by
        dsimp only [J]
        rw [hGzero, matVecMul_zero]
        simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      simp only [hJzero, mul_zero]
      exact tendsto_const_nhds
  have ht := tendsto_integral_of_dominated_convergence (fun x => |J x|)
    (fun k => (hχmeas k).aestronglyMeasurable.mul hiJ.1) hiJ.abs
    (fun k => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (hχbounds k x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχbounds k x).2))
    (Eventually.of_forall hlim)
  have hle : ∀ k, (∫ x, χ k x * J x ∂μ) ≤ 0 := by
    intro k
    have hcut := scalarCutoffFlux_test_nonpos hm hζ0 hζ2 (hδ0 k) (hδε k) hφ hc hs hn
    have heq : (fun x => vecDot (smoothGrad φ x) (scalarCutoffFlux n ζ (δ k) x)) =ᵐ[μ]
        fun x => χ k x * J x := by
      filter_upwards [ae_restrict_of_ae (s := originCube (d := m + 1) 1)
        (scalarCutoffFlux_eq_weightedGradient_ae hm hζ0 hζ2 (hδ0 k))] with x hx
      rw [hx, vecDot_smul_right]
    rw [← integral_congr_ae heq]
    change (∫ x in originCube 1, vecDot (smoothGrad φ x) (scalarCutoffFlux n ζ (δ k) x) ∂volume) ≤ 0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hcut.2
    · intro x hx
      have hz := fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))
      change (∑ i : Fin (m + 1), fderiv ℝ φ x (basisVec i) * scalarCutoffFlux n ζ (δ k) x i) = 0
      simp only [hz, zero_apply, zero_mul, Finset.sum_const_zero]
  exact ⟨hiJ, le_of_tendsto ht (Eventually.of_forall hle)⟩

end

end CoarseDeGiorgi.SharpnessExamples
