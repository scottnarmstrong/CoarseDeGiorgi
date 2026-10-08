module

public import CoarseDeGiorgi.Whitney.SeedProjection
public import CoarseDeGiorgi.Foundations.FracGeometry.Defs
public import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceSupport
public import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceVolume
public import CoarseDeGiorgi.Statements.FracNorm
public import CoarseDeGiorgi.Statements.SurfaceFracNorm

/-!
# Surface patch area

All estimates below use the surface measure `surfaceMeasure`, the sum of the face
measures. In particular, they do not identify this measure with a Hausdorff measure for the ambient
sup metric.
-/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

theorem seedSurfaceMeasure_finite (τ : ℝ) : IsFiniteMeasure (surfaceMeasure (d := d) τ) := by
  change IsFiniteMeasure (Foundations.FracGeometry.surfaceMeasure (d := d) τ)
  infer_instance

end

end CoarseDeGiorgi.Whitney
