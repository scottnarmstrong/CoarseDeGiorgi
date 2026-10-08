module

public import CoarseDeGiorgi.Endpoint.Reconstruction.SmoothReconstruction
public import CoarseDeGiorgi.Weighted.HarmonicCore

/-! # Supported smooth inputs as ordinary and weighted zero-trace functions -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory
open scoped ENNReal Topology
noncomputable section

def smoothUnitH10 {d : ℕ}
    (f : Weighted.supportedCoreSubmodule (CoarseDeGiorgi.originCube (d := d) 1)) : UnitH10 d :=
  H10Function.ofContDiff (isOpen_openCubeSet _) f.property.1 f.property.2.1
    (by rw [← originCube_one_eq_openCubeSet]; exact f.property.2.2)

theorem smoothUnitH10_toFun {d : ℕ}
    (f : Weighted.supportedCoreSubmodule (CoarseDeGiorgi.originCube (d := d) 1)) :
    (smoothUnitH10 f).toH1Function.toFun = f.val := rfl

theorem smoothUnitH10_grad {d : ℕ}
    (f : Weighted.supportedCoreSubmodule (CoarseDeGiorgi.originCube (d := d) 1)) :
    (smoothUnitH10 f).toH1Function.grad = smoothGrad f.val := rfl

theorem smooth_unit_gradient_bounded {d : ℕ}
    (f : Weighted.supportedCoreSubmodule (CoarseDeGiorgi.originCube (d := d) 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ cubeSet (Homogenization.originCube d 0), ‖smoothGrad f.val x‖ ≤ B := by
  have hc : Continuous (smoothGrad f.val) := by
    apply continuous_pi
    intro i
    exact (f.property.1.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨B, hB⟩ := (isBounded_cubeSet (Homogenization.originCube d 0)).isCompact_closure.exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x hx =>
    (hB x (subset_closure hx)).trans (le_max_left _ _)⟩

theorem smooth_unit_memH1a0 {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (f : Weighted.supportedCoreSubmodule (CoarseDeGiorgi.originCube (d := d) 1)) :
    MemH1a0 a (CoarseDeGiorgi.originCube 1) f.val (smoothGrad f.val) :=
  Weighted.memH1a0_of_supported (LowerFractional.lower_unitCube_domain (d := d)).isOpen ha
    f.property.1 f.property.2.1 f.property.2.2

end
end CoarseDeGiorgi.Endpoint.Reconstruction
