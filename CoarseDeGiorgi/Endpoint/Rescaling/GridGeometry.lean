module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import CoarseDeGiorgi.Endpoint.Rescaling.AffineEnergy
public import CoarseDeGiorgi.Endpoint.Rescaling.LatticeCells
public import CoarseDeGiorgi.Endpoint.CubeInterface
public import CoarseDeGiorgi.Endpoint.Interface
public import CoarseDeGiorgi.LowerFractional.CompactCover

/-! Geometry of the fixed grid cubes and their affine parametrizations. -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped ENNReal Pointwise

namespace CoarseDeGiorgi.Endpoint.Rescaling

theorem affineImage_domain {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    IsOpenBoundedConvexDomain (affineImage y r U) := by
  have hS : IsOpenBoundedConvexDomain (r • U) :=
    ⟨hU.isOpen.smul₀ hr.ne', (hU.isBoundedDomain.isBounded.smul₀ r).isBoundedDomain,
      hU.convex.smul r⟩
  exact hS.translateSet y

theorem affineImage_nonempty {d : ℕ} (y : Vec d) (r : ℝ) {U : Set (Vec d)}
    (hne : U.Nonempty) : (affineImage y r U).Nonempty := by
  rw [← affineMap_image]
  exact hne.image _

theorem affineImage_originCube {d : ℕ} (y : Vec d) (ρ : ℝ) :
    affineImage y (1 / 27) (originCube ρ) = gridCube d y ρ := by
  rw [← affineMap_image]
  ext x
  norm_num only [gridCube, CoarseDeGiorgi.originCube, mem_ofPred_eq,
    zpow_neg, zpow_ofNat, Pi.sub_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩ i
    change -(ρ * (1 / 27 : ℝ) / 2) < (1 / 27) * v i + y i - y i ∧
      (1 / 27) * v i + y i - y i < ρ * (1 / 27 : ℝ) / 2
    obtain ⟨hl, hu⟩ := hv i
    constructor <;> linarith only [hl, hu]
  · intro hx
    refine ⟨fun i => 27 * (x i - y i), ?_, ?_⟩
    · intro i
      obtain ⟨hl, hu⟩ := hx i
      constructor <;> linarith only [hl, hu]
    · funext i
      change (1 / 27 : ℝ) * (27 * (x i - y i)) + y i = x i
      ring

/-- Unit containment forces the lattice centers to lie in the finite range used by `latticeIndex`. -/
theorem gridPoint_bounds {d : ℕ} (y : Vec d) (hy : IsGridPoint d y)
    (hsub : gridCube d y 1 ⊆ originCube 1) :
    ∃ z : Fin d → ℤ, y = latticeCenter z ∧ ∀ i, -39 ≤ z i ∧ z i ≤ 39 := by
  classical
  choose z hz using hy
  refine ⟨z, funext hz, ?_⟩
  have hp : (fun i => y i + 1 / 81) ∈ gridCube d y 1 := by
    intro i
    change -(1 * (3 : ℝ) ^ (-3 : ℤ) / 2) < y i + 1 / 81 - y i ∧
      y i + 1 / 81 - y i < 1 * (3 : ℝ) ^ (-3 : ℤ) / 2
    norm_num
  have hm : (fun i => y i - 1 / 81) ∈ gridCube d y 1 := by
    intro i
    change -(1 * (3 : ℝ) ^ (-3 : ℤ) / 2) < y i - 1 / 81 - y i ∧
      y i - 1 / 81 - y i < 1 * (3 : ℝ) ^ (-3 : ℤ) / 2
    norm_num
  intro i
  have hpi := (hsub hp i).2
  have hmi := (hsub hm i).1
  rw [hz i] at hpi hmi
  have hupper : (z i : ℝ) < 40 := by linarith only [hpi]
  have hlower : (-40 : ℝ) < (z i : ℝ) := by linarith only [hmi]
  have hU : z i < 40 := by exact_mod_cast hupper
  have hL : -40 < z i := by exact_mod_cast hlower
  omega

theorem nonnegative_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (u : Vec d → ℝ)
    (hu : ∀ᵐ x ∂(volume.restrict (affineImage y r U)), 0 ≤ u x) :
    ∀ᵐ x ∂(volume.restrict U), 0 ≤ (u ∘ affineMap y r) x := by
  have hm : ∀ᵐ x ∂(Measure.map (affineMap y r) (volume.restrict U)), 0 ≤ u x := by
    rw [map_affineMap_restrict y hr U]
    exact Measure.ae_smul_measure hu _
  exact ae_of_ae_map (affineMap_measurable y r).aemeasurable hm

end CoarseDeGiorgi.Endpoint.Rescaling
