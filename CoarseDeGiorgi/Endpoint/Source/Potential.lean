import CoarseDeGiorgi.Weighted.TestingApproximation
import CoarseDeGiorgi.Weighted.HarmonicCore
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Existence of the potential of a bounded functional on smooth tests (Riesz in `H¹_{a,0}`). -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The energy-Hilbert gradient of a supported smooth test. -/
noncomputable def gradMap (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    supportedCoreSubmodule V →ₗ[ℝ] GradientHilbert ha :=
  ((WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).toLinearMap).comp (supportedGraphMap hV ha)

theorem gradMap_apply (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) (φ : supportedCoreSubmodule V) :
    gradMap hV ha φ = (smoothEnergyField hV ha (isSmoothCore_of_supported ha φ.2.1 φ.2.2.1) :
      GradientHilbert ha) := rfl

theorem gradMap_norm_sq (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) (φ : supportedCoreSubmodule V) :
    ‖gradMap hV ha φ‖ ^ 2 = (weightedEnergy a V (smoothGrad φ.1)).toReal := by
  rw [gradMap_apply, UniformSpace.Completion.norm_coe, GradientCore.norm_sq]
  rfl

theorem gradMap_mem_zero [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (φ : supportedCoreSubmodule V) :
    gradMap hV.isOpen ha φ ∈ zeroSubmodule hV.isOpen ha := by
  have h := (memH1a0_of_supported hV.isOpen ha φ.2.1 φ.2.2.1 φ.2.2.2).gradient_mem hV hne ha
  exact h

/-- The functional `φ ↦ ∫ φ dν` on supported smooth tests. -/
noncomputable def measureFunctional (ν : Measure (Vec d)) [IsFiniteMeasure ν] (V : Set (Vec d)) :
    supportedCoreSubmodule V →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, φ.1 x ∂ν
  map_add' φ ψ := integral_add (φ.2.1.continuous.integrable_of_hasCompactSupport φ.2.2.1)
    (ψ.2.1.continuous.integrable_of_hasCompactSupport ψ.2.2.1)
  map_smul' c φ := by
    change ∫ x, c * φ.1 x ∂ν = c * ∫ x, φ.1 x ∂ν
    exact integral_const_mul c _

/-- Riesz representation: a functional on supported smooth tests that is bounded by the energy
has a potential in `H¹_{a,0}`. -/
theorem exists_potential [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {ν : Measure (Vec d)} [IsFiniteMeasure ν] {M : ℝ}
    (hbd : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V →
      |∫ x, φ x ∂ν| ≤ M * Real.sqrt (weightedEnergy a V (smoothGrad φ)).toReal) :
    ∃ (v : Vec d → ℝ) (Gv : Vec d → Vec d), MemH1a0 a V v Gv ∧
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V →
        ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume = ∫ x, φ x ∂ν := by
  have hbd' : ∀ φ : supportedCoreSubmodule V,
      |measureFunctional ν V φ| ≤ M * ‖gradMap hV.isOpen ha φ‖ := by
    intro φ
    have h := hbd φ.1 φ.2.1 φ.2.2.1 φ.2.2.2
    rw [← Real.sqrt_sq (norm_nonneg (gradMap hV.isOpen ha φ)), gradMap_norm_sq]
    exact h
  have hker : LinearMap.ker (gradMap hV.isOpen ha) ≤ LinearMap.ker (measureFunctional ν V) := by
    intro φ hφ
    have h0 : gradMap hV.isOpen ha φ = 0 := hφ
    have := hbd' φ
    rw [h0, norm_zero, mul_zero] at this
    exact abs_nonpos_iff.mp this
  let f : LinearMap.range (gradMap hV.isOpen ha) →ₗ[ℝ] ℝ :=
    ((LinearMap.ker (gradMap hV.isOpen ha)).liftQ (measureFunctional ν V) hker).comp
      (gradMap hV.isOpen ha).quotKerEquivRange.symm.toLinearMap
  have hf : ∀ φ : supportedCoreSubmodule V,
      f ⟨gradMap hV.isOpen ha φ, LinearMap.mem_range_self _ φ⟩ = measureFunctional ν V φ := by
    intro φ
    change ((LinearMap.ker (gradMap hV.isOpen ha)).liftQ (measureFunctional ν V) hker)
      ((gradMap hV.isOpen ha).quotKerEquivRange.symm ⟨gradMap hV.isOpen ha φ, LinearMap.mem_range_self _ φ⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hfb : ∀ x, ‖f x‖ ≤ M * ‖x‖ := by
    rintro ⟨_, φ, rfl⟩
    rw [Real.norm_eq_abs]
    exact (hf φ).symm ▸ hbd' φ
  let fc := f.mkContinuous M hfb
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range (gradMap hV.isOpen ha)) fc
  have : CompleteSpace (zeroSubmodule hV.isOpen ha) := zeroHilbert_complete hV hne ha
  let L : zeroSubmodule hV.isOpen ha →L[ℝ] ℝ := g.comp (zeroSubmodule hV.isOpen ha).subtypeL
  let z : zeroSubmodule hV.isOpen ha := (InnerProductSpace.toDual ℝ _).symm L
  obtain ⟨v, hv⟩ := zeroHilbert_exists_rep hV hne ha z
  refine ⟨v, (gradientHilbertRep ha z.val).field, hv, ?_⟩
  intro φ hφ hc hs
  let φs : supportedCoreSubmodule V := ⟨φ, hφ, hc, hs⟩
  have h1 : ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) ((gradientHilbertRep ha z.val).field x))
      = inner ℝ (gradMap hV.isOpen ha φs)
        ((gradientHilbertRep ha z.val : GradientCore ha) : GradientHilbert ha) := by
    rw [gradMap_apply, gradientHilbert_inner_coe]
    rfl
  rw [gradientHilbertRep_coe] at h1
  rw [h1, real_inner_comm]
  have h2 : inner ℝ z.val (gradMap hV.isOpen ha φs) =
      inner ℝ z (⟨gradMap hV.isOpen ha φs, gradMap_mem_zero hV hne ha φs⟩ :
        zeroSubmodule hV.isOpen ha) := rfl
  rw [h2, InnerProductSpace.toDual_symm_apply]
  change g (gradMap hV.isOpen ha φs) = _
  rw [show g (gradMap hV.isOpen ha φs) = fc ⟨gradMap hV.isOpen ha φs, LinearMap.mem_range_self _ φs⟩ from
    hg ⟨gradMap hV.isOpen ha φs, LinearMap.mem_range_self _ φs⟩]
  exact hf φs

end CoarseDeGiorgi.Endpoint
