module

public import CoarseDeGiorgi.ExteriorIntegral.Geometry
public import CoarseDeGiorgi.ExteriorIntegral.Algebra
public import CoarseDeGiorgi.ExteriorIntegral.Holder
public import CoarseDeGiorgi.Harnack.Pairing.ArbitraryLayer
public import CoarseDeGiorgi.Harnack.WeakHarnack.SelectionAdapters
public import CoarseDeGiorgi.Selection.SourceRepresentatives
public import CoarseDeGiorgi.Weighted.GradientHilbert
public import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Whitney.LiftZeroExtension
public import CoarseDeGiorgi.Statements.SampledUpperResponse
public import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension

/-! # The layer-by-layer bound for the exterior integral -/

@[expose] public section

namespace CoarseDeGiorgi.ExteriorIntegral

open Homogenization MeasureTheory Set Whitney
open scoped ENNReal

noncomputable section

instance instCountableExteriorCell {d : ℕ} {τ : ℝ} : Countable (ExteriorCell d τ) := by
  unfold ExteriorCell
  infer_instance

theorem isClosed_closedReferenceCube {d : ℕ} (τ : ℝ) :
    IsClosed (closedReferenceCube (d := d) τ) := by
  have : closedReferenceCube (d := d) τ = ⋂ i, {x : Vec d | |x i| ≤ τ / 2} := by
    ext x
    simp [closedReferenceCube]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

end

end CoarseDeGiorgi.ExteriorIntegral
