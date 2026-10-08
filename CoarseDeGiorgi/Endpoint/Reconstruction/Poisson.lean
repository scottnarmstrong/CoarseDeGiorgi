module

public import CoarseDeGiorgi.Endpoint.Reconstruction.DirichletBlock
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessian
public import Homogenization.Sobolev.W1p.CubeVector

/-! # Scalar Dirichlet Poisson existence for duality

The closed zero-trace gradient range is a Hilbert space. The inverse gradient
map is continuous by Poincaré, so scalar `L²` forcing defines a continuous
functional there. Riesz and the closed graph realization give the solution.
-/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

theorem exists_dirichlet_poisson_solution {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (F : Vec d → ℝ) (hF : MemScalarL2 U F) :
    ∃ u : H10Function U, ∀ ψ : H10Function U,
      ∫ x in U, vecDot (u.toH1Function.grad x) (ψ.toH1Function.grad x) =
        ∫ x in U, F x * ψ.toH1Function.toFun x := by
  let T := H10GraphClosed.gradientCLM (d := d) (U := U)
  obtain ⟨K, hK⟩ := H10GraphClosed.exists_antilipschitzWith_gradientCLM hU
  have hclosed : IsClosed (Set.range T) := H10GraphClosed.isClosed_range_gradientCLM hU
  let : CompleteSpace T.range := hclosed.completeSpace_coe
  let e := T.equivRange hK.injective hclosed
  let ℓ : T.range →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ (ScalarL2 U) (toScalarL2 hF)).comp
      (H10GraphClosed.valueCLM.comp e.symm.toContinuousLinearMap)
  let W : T.range := (InnerProductSpace.toDual ℝ T.range).symm ℓ
  let z : H10GraphClosedSpace U := e.symm W
  obtain ⟨u, _, hugrad⟩ := exists_h10Function_of_mem_h10GraphClosedSubmodule hU z.property
  have hTw : T z = (W : HilbertVectorL2 U) :=
    congrArg Subtype.val (e.apply_symm_apply W)
  refine ⟨u, ?_⟩
  intro ψ
  let y : H10GraphClosedSpace U :=
    ⟨(ψ.toH1Function.toScalarL2, ψ.toH1Function.gradToHilbertVectorL2),
      (Submodule.le_topologicalClosure _) (h10_pair_mem_h10GraphSubmodule ψ)⟩
  have hTy : ((e y : T.range) : HilbertVectorL2 U) = ψ.toH1Function.gradToHilbertVectorL2 := rfl
  calc
    ∫ x in U, vecDot (u.toH1Function.grad x) (ψ.toH1Function.grad x) =
        inner ℝ u.toH1Function.gradToHilbertVectorL2 ψ.toH1Function.gradToHilbertVectorL2 :=
      (inner_toHilbertVectorL2OfVecField_eq_integral
        u.toH1Function.grad_memVectorL2 ψ.toH1Function.grad_memVectorL2).symm
    _ = inner ℝ W (e y) := by
      rw [hugrad, ← hTy]
      change inner ℝ (T z) ((e y : T.range) : HilbertVectorL2 U) = _
      rw [hTw]
      rfl
    _ = ℓ (e y) := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := T.range)
      (x := e y) (y := ℓ)
    _ = inner ℝ (toScalarL2 hF) ψ.toH1Function.toScalarL2 := by
      simp only [ℓ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        e.symm_apply_apply, InnerProductSpace.toDual_apply_apply]
      rfl
    _ = ∫ x in U, F x * ψ.toH1Function.toFun x :=
      inner_toScalarL2_eq_integral_mul hF ψ.toH1Function.memL2

theorem exists_unitCube_poisson_solution {d : ℕ} [NeZero d]
    (F : Vec d → ℝ)
    (hF : MemLp F 2 (normalizedCubeMeasure (Homogenization.originCube d 0))) :
    ∃ u : H10Function (openCubeSet (Homogenization.originCube d 0)),
      CubeDirichletWeakPoissonProblem (Homogenization.originCube d 0) u F :=
  exists_dirichlet_poisson_solution (isOpenBoundedConvexDomain_openCubeSet _) F
    (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure _ hF)

/-- Poisson dual solutions carry a genuine `W^{1,p}` gradient whose Jacobian
obeys the Hessian estimate, with one constant before all forcing binders. -/
theorem exists_unitCube_poisson_gradient_bound {d : ℕ} [NeZero d]
    (p : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ F : Vec d → ℝ,
      MemLp F 2 (normalizedCubeMeasure (Homogenization.originCube d 0)) →
      MemLp F p.exponent (normalizedCubeMeasure (Homogenization.originCube d 0)) →
      ∃ u : H10Function (openCubeSet (Homogenization.originCube d 0)),
      ∃ V : CubeVectorW1pFunction (Homogenization.originCube d 0) p,
        CubeDirichletWeakPoissonProblem (Homogenization.originCube d 0) u F ∧
        V.toField = u.toH1Function.grad ∧
        eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) p.exponent
            (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
          C * eLpNorm F p.exponent (normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  obtain ⟨C, hC, hCZ⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le d p
  refine ⟨C, hC, ?_⟩
  intro F hF2 hFp
  obtain ⟨u, hu⟩ := exists_unitCube_poisson_solution F hF2
  obtain ⟨H, hHmem, hHbound⟩ := hCZ 0 F hF2 hFp u hu
  have hrows (i : Fin d) : MemLp (fun x => HilbertVec.ofVec (fun j => H.hess i j x))
      p.exponent (normalizedCubeMeasure (Homogenization.originCube d 0)) := by
    rw [memLp_piLp_iff] at hHmem
    simpa only [Function.comp_apply, HilbertMat.ofMat, PiLp.toLp_apply] using hHmem i
  let V := CubeVectorW1pFunction.ofWeakHessian H hrows
  exact ⟨u, V, hu, CubeVectorW1pFunction.ofWeakHessian_toField H hrows,
    by simpa only [V, CubeVectorW1pFunction.ofWeakHessian_jacobian] using hHbound⟩

end

end CoarseDeGiorgi.Endpoint.Reconstruction
