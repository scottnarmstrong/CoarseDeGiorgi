module

public import CoarseDeGiorgi.Endpoint.Reconstruction.ProjectionPoincare
public import CoarseDeGiorgi.Endpoint.Reconstruction.Poisson
public import CoarseDeGiorgi.Endpoint.Morrey.Smooth

/-! # Cancellation of parent-cell means in Dirichlet duality -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem normalizedCubeMeasure_unit_eq {d : ℕ} :
    normalizedCubeMeasure (Homogenization.originCube d 0) =
      volume.restrict (openCubeSet (Homogenization.originCube d 0)) := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  simp [cubeVolume, cubeScaleFactor_originCube]

theorem integral_mul_projection_eq_zero {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (f g : Vec d → ℝ) (hf : IntegrableOn f (openCubeSet Q))
    (hmean : ∀ R ∈ descendantsAtDepth Q k, ∫ x in openCubeSet R, f x = 0) :
    ∫ x in openCubeSet Q, f x * cubeProjection Q k g x = 0 := by
  have hlocal (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q k) :
      IntegrableOn (fun x => f x * cubeProjection Q k g x) (openCubeSet R) := by
    have hfR := hf.mono_set (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    apply (hfR.mul_const (integralAverage (openCubeSet R) g)).congr
    filter_upwards [cubeProjection_eq_integralAverage_on_cell_ae hR g] with x hx
    rw [hx]
  rw [volume_restrict_openCube_eq_sum_descendants Q k, integral_finsetSum_measure hlocal]
  apply Finset.sum_eq_zero
  intro R hR
  rw [integral_congr_ae (by
    filter_upwards [cubeProjection_eq_integralAverage_on_cell_ae hR g] with x hx
    rw [hx]), integral_mul_const, hmean R hR, zero_mul]

theorem abs_integral_mul_le_lp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} {p s : ℝ} (hps : p.HolderConjugate s)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal s) μ) :
    |∫ x, f x * g x ∂μ| ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal *
      (eLpNorm g (ENNReal.ofReal s) μ).toReal := by
  calc
    |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x * g x‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
    _ ≤ _ := Morrey.integral_mul_norm_le_eLpNorm_toReal hps hf hg

/-- A zero parent-cell mean allows the exact triadic scale to be extracted
from a weak scalar test function. -/
theorem exists_cancellative_scalar_pairing_bound {d : ℕ} [NeZero d]
    {r s : ℝ} (hrs : r.HolderConjugate s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d) (k : ℕ)
      (f : Vec d → ℝ) (u : W1pFunction (openCubeSet Q) (ENNReal.ofReal s))
      (g : Vec d → ℝ),
      MemLp f (ENNReal.ofReal r) (volume.restrict (openCubeSet Q)) →
      MemLp g (ENNReal.ofReal s) (volume.restrict (openCubeSet Q)) →
      (∀ i, ∀ᵐ x ∂volume.restrict (openCubeSet Q), ‖u.grad x i‖ ≤ ‖g x‖) →
      (∀ R ∈ descendantsAtDepth Q k, ∫ x in openCubeSet R, f x = 0) →
      |∫ x in openCubeSet Q, f x * u.toFun x| ≤
        (C * cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ))) *
          (eLpNorm f (ENNReal.ofReal r) (volume.restrict (openCubeSet Q))).toReal *
          (eLpNorm g (ENNReal.ofReal s) (volume.restrict (openCubeSet Q))).toReal := by
  let p : FiniteLpExponent := ⟨ENNReal.ofReal s,
    ENNReal.one_lt_ofReal.mpr hrs.symm.lt, ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC, hbound⟩ := exists_projection_residual_bound (d := d) p
  refine ⟨C, hC, ?_⟩
  intro Q k f u g hf hg hdom hmean
  let μ := volume.restrict (openCubeSet Q)
  let : IsFiniteMeasure μ := (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal s) := hrs.ennrealOfReal
  let H : Vec d → ℝ := fun x => u.toFun x - cubeProjection Q k u.toFun x
  have hHbound := hbound Q k u g hg hdom
  have hH : MemLp H (ENNReal.ofReal s) μ := by
    exact hHbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg)
  have hfu : Integrable (fun x => f x * u.toFun x) μ :=
    memLp_one_iff_integrable.mp (hf.fun_mul u.memLp)
  have hfH : Integrable (fun x => f x * H x) μ :=
    memLp_one_iff_integrable.mp (hf.fun_mul hH)
  have hfP : Integrable (fun x => f x * cubeProjection Q k u.toFun x) μ := by
    convert hfu.sub hfH using 1
    ext x
    dsimp [H]
    ring
  have hzero : ∫ x, f x * cubeProjection Q k u.toFun x ∂μ = 0 :=
    integral_mul_projection_eq_zero Q k f u.toFun
      (hf.integrable (ENNReal.one_le_ofReal.mpr hrs.lt.le)) hmean
  have hpair : ∫ x, f x * u.toFun x ∂μ = ∫ x, f x * H x ∂μ := by
    have heq : (fun x => f x * H x) =
        fun x => f x * u.toFun x - f x * cubeProjection Q k u.toFun x := by
      funext x
      dsimp [H]
      ring
    rw [heq, integral_sub hfu hfP, hzero, sub_zero]
  rw [hpair]
  refine (abs_integral_mul_le_lp hrs hf hH).trans ?_
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top) hHbound
  have hfactor : 0 ≤ C * cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ)) := by
    have : 0 < cubeScaleFactor Q := zpow_pos (by norm_num) _
    positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfactor] at hreal
  calc
    _ ≤ (eLpNorm f (ENNReal.ofReal r) μ).toReal *
        ((C * cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ))) *
          (eLpNorm g (ENNReal.ofReal s) μ).toReal) :=
      mul_le_mul_of_nonneg_left hreal ENNReal.toReal_nonneg
    _ = _ := by ring

theorem exists_cancellative_vector_pairing_bound {d : ℕ} [NeZero d]
    {r s : ℝ} (hrs : r.HolderConjugate s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (F : Vec d → Vec d)
      (V : CubeVectorW1pFunction (Homogenization.originCube d 0)
        ⟨ENNReal.ofReal s, ENNReal.one_lt_ofReal.mpr hrs.symm.lt,
          ENNReal.ofReal_lt_top⟩),
      MemLp F (ENNReal.ofReal r)
        (volume.restrict (openCubeSet (Homogenization.originCube d 0))) →
      (∀ R ∈ descendantsAtDepth (Homogenization.originCube d 0) k,
        ∀ i, ∫ x in openCubeSet R, F x i = 0) →
      |∫ x in openCubeSet (Homogenization.originCube d 0), vecDot (F x) (V.toField x)| ≤
        (C * (3 : ℝ) ^ (-(k : ℤ))) *
          (eLpNorm F (ENNReal.ofReal r)
            (normalizedCubeMeasure (Homogenization.originCube d 0))).toReal *
          (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) (ENNReal.ofReal s)
            (normalizedCubeMeasure (Homogenization.originCube d 0))).toReal := by
  classical
  obtain ⟨C, hC, hscalar⟩ := exists_cancellative_scalar_pairing_bound (d := d) hrs
  refine ⟨d * C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  intro k F V hF hmean
  let Q := Homogenization.originCube d 0
  let μ := volume.restrict (openCubeSet Q)
  let : IsFiniteMeasure μ := (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal s) := hrs.ennrealOfReal
  let g : Vec d → ℝ := fun x => ‖HilbertMat.ofMat (V.jacobian x)‖
  have hg : MemLp g (ENNReal.ofReal s) μ := by
    simpa only [normalizedCubeMeasure_unit_eq] using V.jacobianHilbertMemLp.norm
  have hFi (i : Fin d) : MemLp (fun x => F x i) (ENNReal.ofReal r) μ :=
    (memLp_pi_iff.mp hF) i
  have hFiNorm (i : Fin d) :
      (eLpNorm (fun x => F x i) (ENNReal.ofReal r) μ).toReal ≤
        (eLpNorm F (ENNReal.ofReal r) μ).toReal := by
    apply ENNReal.toReal_mono hF.eLpNorm_ne_top
    exact eLpNorm_mono_ae (hFi i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => norm_le_pi_norm (F x) i)
  have hdom (i j : Fin d) : ∀ᵐ x ∂μ, ‖(V.coord i).grad x j‖ ≤ ‖g x‖ := by
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ‖(HilbertMat.ofMat (V.jacobian x)).ofLp i‖ := by
        simpa only [HilbertMat.ofMat, HilbertVec.ofVec, PiLp.toLp_apply,
            CubeVectorW1pFunction.jacobian_apply] using
          PiLp.norm_apply_le ((HilbertMat.ofMat (V.jacobian x)).ofLp i) j
      _ ≤ _ := PiLp.norm_apply_le (HilbertMat.ofMat (V.jacobian x)) i
  have hprod (i : Fin d) : Integrable (fun x => F x i * V.toField x i) μ :=
    memLp_one_iff_integrable.mp ((hFi i).fun_mul (V.coord i).memLp)
  have hpair (i : Fin d) := hscalar Q k (fun x => F x i) (V.coord i) g
    (hFi i) hg (hdom i) (fun R hR => hmean R hR i)
  have hscale : 0 ≤ C * cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ)) := by
    have : 0 < cubeScaleFactor Q := zpow_pos (by norm_num) _
    positivity
  calc
    |∫ x in openCubeSet Q, vecDot (F x) (V.toField x)| =
        |∑ i : Fin d, ∫ x, F x i * V.toField x i ∂μ| := by
      rw [show (fun x => vecDot (F x) (V.toField x)) =
          fun x => ∑ i : Fin d, F x i * V.toField x i by rfl,
        integral_finsetSum _ (fun i _ => hprod i)]
    _ ≤ ∑ i : Fin d, |∫ x, F x i * V.toField x i ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d,
        (C * cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ))) *
          (eLpNorm F (ENNReal.ofReal r) μ).toReal *
          (eLpNorm g (ENNReal.ofReal s) μ).toReal := by
      apply Finset.sum_le_sum
      intro i _
      exact (hpair i).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hFiNorm i) hscale) ENNReal.toReal_nonneg)
    _ = _ := by
      have hJ : AEStronglyMeasurable (fun x => HilbertMat.ofMat (V.jacobian x)) μ := by
        simpa only [normalizedCubeMeasure_unit_eq] using V.jacobianHilbertMemLp.aestronglyMeasurable
      rw [show eLpNorm g (ENNReal.ofReal s) μ =
        eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) (ENNReal.ofReal s) μ from
          eLpNorm_norm _ hJ]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        normalizedCubeMeasure_unit_eq, μ, Q, cubeScaleFactor_originCube, zpow_zero, mul_one]
      ring

end

end CoarseDeGiorgi.Endpoint.Reconstruction
