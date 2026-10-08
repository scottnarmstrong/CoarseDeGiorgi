module

public import CoarseDeGiorgi.SharpnessExamples.ScalarSumValue
public import CoarseDeGiorgi.Weighted.PairOperations

/-! # Convergence of the cylinder series in the weighted completion -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem scalar_identity_quadratic {d : ℕ} (w : ℝ) (g : Vec d) :
    vecDot g (matVecMul (w • (1 : Mat d)) g) = w * vecNormSq g := by
  have h1 : matVecMul (1 : Mat d) g = g := by
    ext i
    simp [matVecMul, Matrix.one_apply]
  rw [smul_matVecMul, h1, vecDot_smul_right]
  rfl

/-- The explicit partial gradients converge in weighted energy. -/
theorem scalarSubsolutionSum_tendsto_energy {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    Tendsto (fun k => weightedEnergy
      (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1))) (originCube 1)
      ((fun x : Vec (m + 1) => ∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x) -
        scalarSubsolutionGradientSum ζ)) atTop (𝓝 0) := by
  classical
  let μ := volume.restrict (originCube (d := m + 1) 1)
  let w := scalarSharpnessWeight (d := m + 1) ζ (cylinderRadialConstant (m + 1))
  let G := scalarSubsolutionGradientSum (d := m + 1) ζ
  let F := fun k (x : Vec (m + 1)) => ∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x
  let e := fun x => w x * (scalarSubsolutionSum ζ x ^ 2 + vecNormSq (G x))
  have hw : ∀ x, 0 < w x := scalarSharpnessWeight_pos (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))
  have he : ∀ x, 0 ≤ e x := fun x => mul_nonneg (hw x).le
    (add_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
  have hie : Integrable e μ := scalarSubsolutionSum_density_integrable hm hζ0 hζ2
  have hG : AEStronglyMeasurable G μ := scalarSubsolutionGradientSum_aestronglyMeasurable hm hζ0 hζ2
  have hF : ∀ k, AEStronglyMeasurable (F k) μ := by
    intro k
    have h : AEStronglyMeasurable (∑ j ∈ Finset.range k,
        scalarCylinderGradient (d := m + 1) j ζ) μ :=
      Finset.aestronglyMeasurable_sum _ (fun j _ =>
        (scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 j).2.1)
    have heq : (∑ j ∈ Finset.range k, scalarCylinderGradient (d := m + 1) j ζ) = F k := by
      funext x
      simp only [Finset.sum_apply, F]
    rwa [heq] at h
  have hnorm : Continuous (fun z : Vec (m + 1) => vecNormSq z) := by
    unfold vecNormSq vecDot
    fun_prop
  have hmF : ∀ k, AEMeasurable (fun x => ENNReal.ofReal (w x * vecNormSq (F k x - G x))) μ := by
    intro k
    exact ((scalarSharpnessWeight_measurable ζ (cylinderRadialConstant (m + 1))).aestronglyMeasurable.mul
      (hnorm.comp_aestronglyMeasurable ((hF k).sub hG))).aemeasurable.ennreal_ofReal
  have hb : ∀ k, (fun x => ENNReal.ofReal (w x * vecNormSq (F k x - G x))) ≤ᵐ[μ]
      fun x => ENNReal.ofReal (e x) := by
    intro k
    apply Eventually.of_forall
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (hw x).le
    exact (scalarCylinder_partial_error_bounds (by omega) hζ0 hζ2 x k).2.trans
      (le_add_of_nonneg_left (sq_nonneg _))
  have ht := tendsto_lintegral_of_dominated_convergence'
    (fun x => ENNReal.ofReal (e x)) hmF hb
    ((lintegral_ofReal_ne_top_iff_integrable hie.1 (Eventually.of_forall he)).mpr hie)
    (f := fun _ => (0 : ℝ≥0∞)) (Eventually.of_forall (fun x => ?_))
  · simpa only [weightedEnergy, CoarseDeGiorgi.weightedEnergy, scalarSharpnessCoefficient,
      scalar_identity_quadratic, Pi.sub_apply, F, G, μ, lintegral_zero] using ht
  · apply tendsto_const_nhds.congr'
    filter_upwards [scalarCylinder_partials_eventually_eq (by omega) hζ0 hζ2 x] with k hk
    simp only [F, G, hk.2, sub_self, vecNormSq, vecDot, Pi.zero_apply,
      Finset.sum_const_zero, mul_zero, ENNReal.ofReal_zero]

theorem scalarCylinder_partial_memH1a {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (k : ℕ) :
    MemH1a (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1))) (originCube 1)
      (fun x : Vec (m + 1) => ∑ j ∈ Finset.range k, scalarCylinderSubsolution j ζ x)
      (fun x => ∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x) := by
  classical
  have hV := Whitney.source_cube_domain (d := m + 1) (by norm_num : (0 : ℝ) < 1)
  have hne := Whitney.source_cube_nonempty (d := m + 1) (by norm_num : (0 : ℝ) < 1)
  have ha := scalarSharpnessCoefficient_isWeightedCoeffOn (d := m + 1) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))
  induction k with
  | zero =>
    have h := scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 0
    simpa only [Weighted.MemH1a, Finset.range_zero, Finset.sum_empty, sub_self, Pi.zero_def] using
      Weighted.MemH1a.sub hV hne ha h h
  | succ k ih =>
    simpa only [Weighted.MemH1a, Finset.sum_range_succ, Pi.add_def] using
      Weighted.MemH1a.add hV hne ha ih (scalarCylinderSubsolution_memH1a_explicit hm hζ0 hζ2 k)

/-- The literal sum of the source's cylinder profiles is in `H¹_a`, with the
literal gradient series. No convergence or membership premise is added. -/
theorem scalarSubsolutionSum_memH1a {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    MemH1a (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1))) (originCube 1)
      (scalarSubsolutionSum (d := m + 1) ζ) (scalarSubsolutionGradientSum ζ) :=
  Weighted.memH1a_of_tendsto (Whitney.source_cube_domain (by norm_num))
    (Whitney.source_cube_nonempty (by norm_num))
    (scalarSharpnessCoefficient_isWeightedCoeffOn (by omega) hζ0 hζ2
      (cylinderRadialConstant_pos (d := m + 1) (by omega)))
    (scalarCylinder_partial_memH1a hm hζ0 hζ2)
    (scalarSubsolutionSum_integrable hm hζ0 hζ2)
    (scalarSubsolutionGradientSum_aestronglyMeasurable hm hζ0 hζ2)
    (scalarSubsolutionSum_tendsto_l1 hm hζ0 hζ2)
    (scalarSubsolutionSum_tendsto_energy hm hζ0 hζ2)

end

end CoarseDeGiorgi.SharpnessExamples
