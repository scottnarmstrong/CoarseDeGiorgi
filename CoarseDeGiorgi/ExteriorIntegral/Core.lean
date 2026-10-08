import CoarseDeGiorgi.ExteriorIntegral.Geometry
import CoarseDeGiorgi.ExteriorIntegral.Algebra
import CoarseDeGiorgi.ExteriorIntegral.Holder
import CoarseDeGiorgi.Harnack.Pairing.ArbitraryLayer
import CoarseDeGiorgi.Harnack.WeakHarnack.SelectionAdapters
import CoarseDeGiorgi.Selection.SourceRepresentatives
import CoarseDeGiorgi.Weighted.GradientHilbert
import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Whitney.LiftZeroExtension
import CoarseDeGiorgi.Statements.SampledUpperResponse
import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension

/-! # The layer-by-layer bound for the exterior integral -/

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
