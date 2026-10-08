import CoarseDeGiorgi.Endpoint.Reconstruction.Cancellation
import CoarseDeGiorgi.Endpoint.Reconstruction.ScalarDuality

/-! # Dirichlet scale cancellation by Poisson Hessian duality -/

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem dirichlet_poisson_cross_pairing {d : ℕ} [NeZero d]
    (F : Vec d → Vec d) (φ : Vec d → ℝ)
    (w z : H10Function (openCubeSet (Homogenization.originCube d 0)))
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Mat d))
      (openCubeSet (Homogenization.originCube d 0)) w F)
    (hz : CubeDirichletWeakPoissonProblem (Homogenization.originCube d 0) z φ) :
    ∫ x in openCubeSet (Homogenization.originCube d 0), w.toH1Function.toFun x * φ x =
      ∫ x in openCubeSet (Homogenization.originCube d 0),
        vecDot (F x) (z.toH1Function.grad x) := by
  have hone (x : Vec d) : matVecMul (1 : Mat d) x = x := by
    funext i
    simp only [matVecMul, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc
    _ = ∫ x in openCubeSet (Homogenization.originCube d 0), φ x * w.toH1Function.toFun x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = ∫ x in openCubeSet (Homogenization.originCube d 0),
        vecDot (z.toH1Function.grad x) (w.toH1Function.grad x) := (hz w).symm
    _ = ∫ x in openCubeSet (Homogenization.originCube d 0),
        vecDot (w.toH1Function.grad x) (z.toH1Function.grad x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact vecDot_comm _ _
    _ = _ := by simpa only [hone] using hw z

/-- The constant is fixed before every depth, datum and solution. Parent-cell
mean cancellation gives the full factor `3^{-k}` without a scale loss. -/
theorem exists_unitCube_dirichlet_cancellation_bound {d : ℕ} [NeZero d]
    {r s : ℝ} (hrs : r.HolderConjugate s) (hr2 : r < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (F : Vec d → Vec d),
      MemLp F (ENNReal.ofReal r)
        (normalizedCubeMeasure (Homogenization.originCube d 0)) →
      (∀ R ∈ descendantsAtDepth (Homogenization.originCube d 0) k,
        ∀ i, ∫ x in openCubeSet R, F x i = 0) →
      ∀ w : H10Function (openCubeSet (Homogenization.originCube d 0)),
        IsZeroTraceDirichletRhsWeakSolution (fun _ : Vec d => (1 : Mat d))
          (openCubeSet (Homogenization.originCube d 0)) w F →
        eLpNorm w.toH1Function.toFun (ENNReal.ofReal r)
            (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-(k : ℤ))) *
            eLpNorm F (ENNReal.ofReal r)
              (normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  let p : FiniteLpExponent := ⟨ENNReal.ofReal s,
    ENNReal.one_lt_ofReal.mpr hrs.symm.lt, ENNReal.ofReal_lt_top⟩
  obtain ⟨CP, hCP, hpair⟩ := exists_cancellative_vector_pairing_bound (d := d) hrs
  obtain ⟨CZ, hCZ, hpoisson⟩ := exists_unitCube_poisson_gradient_bound (d := d) p
  refine ⟨CP * CZ.toReal, mul_nonneg hCP ENNReal.toReal_nonneg, ?_⟩
  intro k F hF hmean w hw
  let μ := normalizedCubeMeasure (Homogenization.originCube d 0)
  have hw2 : MemLp w.toH1Function.toFun 2 μ := by
    simpa only [μ, normalizedCubeMeasure_unit_eq] using w.toH1Function.memL2
  have hFopen : MemLp F (ENNReal.ofReal r)
      (volume.restrict (openCubeSet (Homogenization.originCube d 0))) := by
    simpa only [normalizedCubeMeasure_unit_eq] using hF
  have hscale : 0 ≤ CP * (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hK : 0 ≤ ((CP * CZ.toReal) * (3 : ℝ) ^ (-(k : ℤ))) *
      (eLpNorm F (ENNReal.ofReal r) μ).toReal := by positivity
  have hnorm := scalar_lp_duality_of_memL2 hrs hr2 hw2 hK (by
    intro φ hφ2 hφs
    obtain ⟨z, V, hz, hV, hHbound⟩ := hpoisson φ hφ2 hφs
    have hh := hpair k F V hFopen hmean
    rw [hV, ← dirichlet_poisson_cross_pairing F φ w z hw hz,
      ← normalizedCubeMeasure_unit_eq] at hh
    have hHreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hCZ.ne hφs.eLpNorm_ne_top) hHbound
    rw [ENNReal.toReal_mul] at hHreal
    calc
      _ ≤ (CP * (3 : ℝ) ^ (-(k : ℤ))) *
          (eLpNorm F (ENNReal.ofReal r) μ).toReal *
          (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) (ENNReal.ofReal s) μ).toReal := hh
      _ ≤ (CP * (3 : ℝ) ^ (-(k : ℤ))) *
          (eLpNorm F (ENNReal.ofReal r) μ).toReal *
          (CZ.toReal * (eLpNorm φ (ENNReal.ofReal s) μ).toReal) :=
        mul_le_mul_of_nonneg_left hHreal (mul_nonneg hscale ENNReal.toReal_nonneg)
      _ = (((CP * CZ.toReal) * (3 : ℝ) ^ (-(k : ℤ))) *
          (eLpNorm F (ENNReal.ofReal r) μ).toReal) *
          (eLpNorm φ (ENNReal.ofReal s) μ).toReal := by ring)
  refine hnorm.trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hF.eLpNorm_ne_top]

end

end CoarseDeGiorgi.Endpoint.Reconstruction
