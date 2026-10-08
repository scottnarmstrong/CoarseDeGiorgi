module

public import CoarseDeGiorgi.Statements.OriginCube
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.H10Adjoint
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.DirichletNeumannEndpoint

/-! # Dirichlet blocks on the unit cube

These lemmas construct zero-trace Dirichlet blocks on the unit cube. The
forcing has the sign giving
`∫ ∇w · ∇ψ = ∫ G · ∇ψ`. Constants in the gradient estimate depend only on the
dimension and the finite exponent.
-/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

theorem originCube_one_eq_openCubeSet (d : ℕ) :
    CoarseDeGiorgi.originCube (d := d) 1 =
      openCubeSet (Homogenization.originCube d 0) := by
  ext x
  simp only [CoarseDeGiorgi.originCube, openCubeSet, Homogenization.originCube,
    cubeScaleFactor, zpow_zero, Pi.zero_apply, Int.cast_zero, zero_sub,
    zero_add, mul_one]

/-- Every square-integrable vector field supplies a zero-trace Dirichlet block.
This construction requires no regularity or ellipticity of the weighted field. -/
theorem exists_unitCube_dirichlet_block {d : ℕ} [NeZero d]
    (G : Vec d → Vec d)
    (hG : MemVectorL2 (openCubeSet (Homogenization.originCube d 0)) G) :
    ∃ w : H10Function (openCubeSet (Homogenization.originCube d 0)),
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet (Homogenization.originCube d 0)) w G := by
  obtain ⟨w, hw, _⟩ :=
    CubeCalderonZygmund.exists_openCubeSetScalarDivergenceSolution
      (Homogenization.originCube d 0) (by norm_num : (0 : ℝ) < 1)
      (fun x => -G x) hG.neg
  refine ⟨w, ?_⟩
  intro ψ
  have h := hw ψ
  simp only [one_mul, vecDot_neg_left, integral_neg, neg_neg] at h
  have hone (x : Vec d) : matVecMul (1 : Mat d) x = x := by
    funext i
    simp only [matVecMul, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simpa only [hone] using h

/-- The divergence estimate supplies the gradient regularity used by Morrey.
The same constant works for every forcing and every solution on the unit cube. -/
theorem exists_unitCube_dirichlet_gradient_bound {d : ℕ} (hd : 2 ≤ d)
    (p : ℝ≥0∞) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Vec d → Vec d),
        MemLp G p (normalizedCubeMeasure (Homogenization.originCube d 0)) →
        ∀ w : H10Function (openCubeSet (Homogenization.originCube d 0)),
          IsZeroTraceDirichletRhsWeakSolution
            (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
            (openCubeSet (Homogenization.originCube d 0)) w G →
          MemLp w.toH1Function.grad p
              (normalizedCubeMeasure (Homogenization.originCube d 0)) ∧
            cubeLpNorm (Homogenization.originCube d 0) p w.toH1Function.grad ≤
              C * cubeLpNorm (Homogenization.originCube d 0) p G := by
  obtain ⟨C, hC, hbound⟩ :=
    CubeCalderonZygmund.exists_cubeDirichletNeumannDivergence_cz hd p hp hptop
  refine ⟨C, hC, ?_⟩
  intro G hG w hw
  have hneg : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
      (openCubeSet (Homogenization.originCube d 0)) w (fun x => -(-G x)) := by
    simpa only [neg_neg] using hw
  obtain ⟨hgrad, hnorm⟩ :=
    (hbound (Homogenization.originCube d 0) (fun x => -G x) hG.neg).1 w hneg
  refine ⟨hgrad, ?_⟩
  change cubeLpNorm (Homogenization.originCube d 0) p w.toH1Function.grad ≤
    C * cubeLpNorm (Homogenization.originCube d 0) p (-G) at hnorm
  simpa only [cubeLpNorm, eLpNorm_neg] using hnorm

end CoarseDeGiorgi.Endpoint.Reconstruction
