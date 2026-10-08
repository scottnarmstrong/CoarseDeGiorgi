import CoarseDeGiorgi.Endpoint.Reconstruction.DirichletAlgebra

/-! # The elementary Dirichlet L2 stability estimate -/

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

theorem dirichlet_gradient_l2_norm_le {d : ℕ} (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet (Homogenization.originCube d 0)) F)
    (w : UnitH10 d) (hw : UnitDirichletEquation w F) :
    ‖w.toH1Function.gradToHilbertVectorL2‖ ≤ ‖toHilbertVectorL2OfVecField hF‖ := by
  let V := w.toH1Function.gradToHilbertVectorL2
  let H := toHilbertVectorL2OfVecField hF
  have heq := hw w
  simp only [matVecMul_one] at heq
  rw [← inner_toHilbertVectorL2OfVecField_eq_integral
    w.toH1Function.grad_memVectorL2 w.toH1Function.grad_memVectorL2,
    ← inner_toHilbertVectorL2OfVecField_eq_integral hF w.toH1Function.grad_memVectorL2] at heq
  change inner ℝ V V = inner ℝ H V at heq
  rw [real_inner_self_eq_norm_sq] at heq
  have hbound : ‖V‖ ^ 2 ≤ ‖H‖ * ‖V‖ := by
    rw [heq]
    exact real_inner_le_norm _ _
  change ‖V‖ ≤ ‖H‖
  by_cases hzero : ‖V‖ = 0
  · simpa only [hzero] using norm_nonneg H
  have hpos : 0 < ‖V‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  nlinarith

/-- A single constant controls every positive-sign Dirichlet solution on the
unit cube in L2, using the Hilbert norm of the datum. -/
theorem exists_dirichlet_value_l2_bound {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Vec d → Vec d)
      (_hF : MemVectorL2 (openCubeSet (Homogenization.originCube d 0)) F)
      (w : UnitH10 d), UnitDirichletEquation w F →
      eLpNorm w.toH1Function.toFun 2
          (volume.restrict (openCubeSet (Homogenization.originCube d 0))) ≤
        ENNReal.ofReal C * eLpNorm (hilbertifyVecField F) 2
          (volume.restrict (openCubeSet (Homogenization.originCube d 0))) := by
  obtain ⟨C, hC, hP⟩ := h10GraphClosedSubmodule_exists_norm_value_le_mul_norm_gradient
    (isOpenBoundedConvexDomain_openCubeSet (Homogenization.originCube d 0))
  refine ⟨C, hC, ?_⟩
  intro F hF w hw
  have hgraph := hP (w.toH1Function.toScalarL2, w.toH1Function.gradToHilbertVectorL2)
    ((Submodule.le_topologicalClosure _) (h10_pair_mem_h10GraphSubmodule w))
  have hnorm := hgraph.trans (mul_le_mul_of_nonneg_left (dirichlet_gradient_l2_norm_le F hF w hw) hC)
  have hreal : (eLpNorm w.toH1Function.toFun 2
      (volume.restrict (openCubeSet (Homogenization.originCube d 0)))).toReal ≤
      C * (eLpNorm (hilbertifyVecField F) 2
        (volume.restrict (openCubeSet (Homogenization.originCube d 0)))).toReal := by
    simpa only [H1Function.toScalarL2, toScalarL2, toHilbertVectorL2OfVecField,
      toHilbertVectorL2, Lp.norm_toLp, volumeMeasureOn] using hnorm
  have hH := memHilbertVectorL2_hilbertifyVecField hF
  have hh := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_toReal w.toH1Function.memL2.eLpNorm_ne_top,
    ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hH.eLpNorm_ne_top] at hh

end

end CoarseDeGiorgi.Endpoint.Reconstruction
