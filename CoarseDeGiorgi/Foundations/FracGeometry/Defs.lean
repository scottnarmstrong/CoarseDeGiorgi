import Homogenization.Multiscale.CubeAverage
import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod

import CoarseDeGiorgi.Foundations.Euclid.Gagliardo
import CoarseDeGiorgi.Statements.EuclidDist
import CoarseDeGiorgi.Statements.FracSeminorm
import CoarseDeGiorgi.Statements.FracNorm
import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Statements.CubeFaceMeasure
import CoarseDeGiorgi.Statements.SurfaceMeasure
import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
import CoarseDeGiorgi.Statements.SurfaceFracNorm

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/- Compatibility names retain the existing implementation API while all mathematical
bodies are supplied by the `Statements/` definitions. -/
/-- Compatibility name for the Euclidean distance. -/
abbrev euclidDist {d : ℕ} (x y : Vec d) : ℝ :=
  CoarseDeGiorgi.euclidDist x y

/-- Compatibility name for the Euclidean Gagliardo seminorm. -/
abbrev fracSeminorm {d : ℕ} (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  CoarseDeGiorgi.fracSeminorm V α r w

/-- Compatibility name for the fractional Sobolev norm. -/
abbrev fracNorm {d : ℕ} (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  CoarseDeGiorgi.fracNorm V α r w

/-- Compatibility name for the centered cube boundary. -/
abbrev cubeSurface {d : ℕ} (τ : ℝ) : Set (Vec d) :=
  CoarseDeGiorgi.cubeSurface τ

/-- Compatibility name for the surface measure, the sum of the face measures. -/
abbrev surfaceMeasure {d : ℕ} (τ : ℝ) : Measure (Vec d) :=
  CoarseDeGiorgi.surfaceMeasure τ

/-- Compatibility name for the surface fractional seminorm. -/
abbrev surfaceFracSeminorm {d : ℕ} (τ α r : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  CoarseDeGiorgi.surfaceFracSeminorm τ α r f

/-- Compatibility name for the surface fractional norm. -/
abbrev surfaceFracNorm {d : ℕ} (τ α r : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  CoarseDeGiorgi.surfaceFracNorm τ α r f

variable {d : ℕ}

/-- Compatibility access to the coordinate-face measure for Fubini arguments. -/
abbrev faceMeasure (τ : ℝ) (i : Fin d) (positive : Bool) : Measure (Vec d) :=
  CoarseDeGiorgi.cubeFaceMeasure τ i positive

theorem faceMeasure_eq_pi (τ : ℝ) (i : Fin d) (positive : Bool) :
    faceMeasure τ i positive = Measure.pi (fun j : Fin d =>
      if j = i then Measure.dirac (if positive then τ / 2 else -τ / 2)
      else volume.restrict (Set.Ioo (-τ / 2) (τ / 2))) := rfl

theorem surfaceMeasure_eq_sum_faceMeasure (τ : ℝ) :
    surfaceMeasure (d := d) τ = ∑ i : Fin d, ∑ positive : Bool,
      faceMeasure τ i positive := rfl

/-- The Euclidean distance is definitionally the infrastructure distance. -/
theorem euclidDist_eq_eDist2 (x y : Vec d) :
    euclidDist x y = Euclid.eDist2 x y := rfl

/-- The fractional seminorm is definitionally the Euclidean comparison seminorm. -/
theorem fracSeminorm_eq_eFracSeminorm (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) :
    fracSeminorm V α r w = Euclid.eFracSeminorm V α r w := rfl

/-- The surface kernel has the intrinsic dimension `d-1`. -/
theorem surfaceFracSeminorm_eq_lintegral (τ α r : ℝ) (w : Vec d → ℝ) :
    surfaceFracSeminorm τ α r w =
      (∫⁻ xy, Euclid.euclidKernel ((d : ℝ) - 1 + α * r) r w xy
        ∂((surfaceMeasure τ).prod (surfaceMeasure τ))) ^ (1 / r) := rfl

/-- The full norm's positive power is its defining power sum. -/
theorem fracNorm_rpow (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Vec d → ℝ) :
    fracNorm V α r w ^ r =
      eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ^ r + fracSeminorm V α r w ^ r := by
  unfold fracNorm CoarseDeGiorgi.fracNorm
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

/-- The analogous surface power identity keeps every cross-face term. -/
theorem surfaceFracNorm_rpow (τ α : ℝ) {r : ℝ} (hr : 0 < r) (w : Vec d → ℝ) :
    surfaceFracNorm τ α r w ^ r =
      eLpNorm w (ENNReal.ofReal r) (surfaceMeasure τ) ^ r + surfaceFracSeminorm τ α r w ^ r := by
  unfold surfaceFracNorm CoarseDeGiorgi.surfaceFracNorm
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

/-- The full norm controls its Lebesgue component. -/
theorem eLpNorm_le_fracNorm (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Vec d → ℝ) :
    eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ≤ fracNorm V α r w := by
  rw [← ENNReal.rpow_le_rpow_iff hr, fracNorm_rpow V α hr w]
  exact le_add_right le_rfl

/-- The full norm controls its seminorm component. -/
theorem fracSeminorm_le_fracNorm (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Vec d → ℝ) : fracSeminorm V α r w ≤ fracNorm V α r w := by
  rw [← ENNReal.rpow_le_rpow_iff hr, fracNorm_rpow V α hr w]
  exact le_add_left le_rfl

private instance faceCoordinateMeasures_finite (τ : ℝ) (i : Fin d) (positive : Bool)
    (j : Fin d) : IsFiniteMeasure (CoarseDeGiorgi.faceCoordinateMeasures τ i positive j) := by
  unfold CoarseDeGiorgi.faceCoordinateMeasures
  split_ifs <;> infer_instance

private instance cubeFaceMeasure_finite (τ : ℝ) (i : Fin d) (positive : Bool) :
    IsFiniteMeasure (CoarseDeGiorgi.cubeFaceMeasure τ i positive) := by
  unfold CoarseDeGiorgi.cubeFaceMeasure
  infer_instance

instance faceMeasure_finite (τ : ℝ) (i : Fin d) (positive : Bool) :
    IsFiniteMeasure (faceMeasure τ i positive) := by
  unfold faceMeasure
  infer_instance

/-- The surface measure (sum of face measures) is finite, even at an inadmissible radius. -/
instance surfaceMeasure_finite (τ : ℝ) : IsFiniteMeasure (surfaceMeasure (d := d) τ) := by
  unfold surfaceMeasure CoarseDeGiorgi.surfaceMeasure
  infer_instance

/-- The zero-dimensional surface has no faces. -/
theorem surfaceMeasure_zero_dim (τ : ℝ) : surfaceMeasure (d := 0) τ = 0 := by
  simp only [surfaceMeasure, CoarseDeGiorgi.surfaceMeasure, Finset.univ_eq_empty, Finset.sum_empty]

end

end CoarseDeGiorgi.Foundations.FracGeometry
