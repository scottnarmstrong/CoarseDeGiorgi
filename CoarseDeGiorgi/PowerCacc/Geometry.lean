module

public import CoarseDeGiorgi.Assembly.LocalBoundedness
public import CoarseDeGiorgi.Whitney.Interpolation.BoundsAff
public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.DomainSplit
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.IsSmoothCore
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Cube geometry and Lipschitz regularity of smooth cores on `τ□̄₀` -/

@[expose] public section

namespace CoarseDeGiorgi.PowerCacc

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

variable {d : ℕ}

theorem originCube_eq_pi (τ : ℝ) :
    originCube (d := d) τ = Set.pi univ (fun _ => Ioo (-(τ / 2)) (τ / 2)) := by
  ext x
  simp [originCube]

theorem closedReferenceCube_eq_pi (τ : ℝ) :
    closedReferenceCube (d := d) τ = Set.pi univ (fun _ => Icc (-(τ / 2)) (τ / 2)) := by
  ext x
  simp only [closedReferenceCube, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_true_left, mem_Icc,
    abs_le]

theorem closure_originCube_eq {τ : ℝ} (hτ : 0 < τ) :
    closure (originCube (d := d) τ) = closedReferenceCube τ := by
  rw [originCube_eq_pi, closure_pi_set, closedReferenceCube_eq_pi]
  congr 1
  funext i
  exact closure_Ioo (by linarith)

theorem originCube_subset_closedReferenceCube (τ : ℝ) :
    originCube (d := d) τ ⊆ closedReferenceCube τ := by
  intro x hx i
  exact abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩

theorem closedReferenceCube_subset_originCube {τ ρ : ℝ} (h : τ < ρ) :
    closedReferenceCube (d := d) τ ⊆ originCube ρ := by
  intro x hx i
  have := abs_le.mp (hx i)
  constructor <;> linarith [this.1, this.2]

theorem cubeSurface_subset_closedReferenceCube (τ : ℝ) :
    cubeSurface (d := d) τ ⊆ closedReferenceCube τ := by
  intro x hx i
  have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  have h2 : ‖x‖ = τ / 2 := hx
  rw [Real.norm_eq_abs] at h1
  linarith

theorem isCompact_closedReferenceCube (τ : ℝ) :
    IsCompact (closedReferenceCube (d := d) τ) := by
  rw [closedReferenceCube_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem isOpen_originCube (τ : ℝ) : IsOpen (originCube (d := d) τ) := by
  rw [originCube_eq_pi]
  exact isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem isOpen_exterior {τ : ℝ} :
    IsOpen (originCube (d := d) 1 \ closedReferenceCube τ) :=
  (isOpen_originCube 1).sdiff (WhitneyInterp.isClosed_closedReferenceCube)

/-- The exterior integral over `□₀ ∖ τ□̄₀` equals that over `□₀ ∖ τ□₀`. -/
theorem integral_exterior_closedReferenceCube {τ : ℝ} (hτ : 0 < τ) (V : Set (Vec d))
    (hU : IsOpenBoundedConvexDomain (originCube (d := d) τ)) (f : Vec d → ℝ) :
    ∫ x in V \ originCube τ, f x = ∫ x in V \ closedReferenceCube τ, f x := by
  rw [Harnack.PowerCaccioppoli.integral_exterior_eq_closure_exterior hU f,
    closure_originCube_eq hτ]

/-- A smooth core is Lipschitz on the closed cube `τ□̄₀` for `τ < 1`. -/
theorem lipschitzOn_closedReferenceCube_of_isSmoothCore {a : CoeffField d} {f : Vec d → ℝ}
    {τ : ℝ} (hτ : τ < 1) (hf : IsSmoothCore a (originCube 1) f) :
    ∃ K : ℝ≥0, LipschitzOnWith K f (closedReferenceCube τ) := by
  have hconv : Convex ℝ (originCube (d := d) 1) := by
    rw [originCube_eq_pi]
    exact convex_pi fun _ _ => convex_Ioo _ _
  have hloc := (hf.1.of_le (by norm_num)).locallyLipschitzOn hconv
  exact (hloc.mono (closedReferenceCube_subset_originCube hτ)).exists_lipschitzOnWith_of_compact
    (isCompact_closedReferenceCube τ)

end CoarseDeGiorgi.PowerCacc
