module

public import CoarseDeGiorgi.Selection.CoareaPartition
public import CoarseDeGiorgi.Selection.Maximal

@[expose] public section

namespace CoarseDeGiorgi.Selection

open Homogenization MeasureTheory Set Metric
open scoped ENNReal BigOperators

noncomputable section

/-- Surface energy extended by zero outside the prescribed radius interval. -/
def surfaceEnergyMeasure {d : ℕ} (ρ R : ℝ) (g : Vec d → ℝ≥0∞) : Measure ℝ :=
  (volume.restrict (Ioo ρ R)).withDensity (fun τ => ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ)

/-- The source centered surface-energy maximal function, for an abstract nonnegative density. -/
def surfaceEnergyMaximal {d : ℕ} (ρ R : ℝ) (g : Vec d → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  centeredMaximal (surfaceEnergyMeasure ρ R g)

variable {n : ℕ}

theorem surfaceEnergyMeasure_univ {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    surfaceEnergyMeasure ρ R g univ = 2 * ∫⁻ x in cubicalAnnulus (n + 1) ρ R, g x := by
  rw [surfaceEnergyMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact cubical_coarea hρ hg

theorem surfaceEnergyMeasure_ball (ρ R τ r : ℝ)
    {g : Vec (n + 1) → ℝ≥0∞} :
    surfaceEnergyMeasure ρ R g (ball τ r) =
      ∫⁻ l in ball τ r ∩ Ioo ρ R, ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure l := by
  rw [surfaceEnergyMeasure, withDensity_apply _ isOpen_ball.measurableSet,
    Measure.restrict_restrict isOpen_ball.measurableSet]


theorem surfaceEnergyMeasure_finite {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g)
    (hfinite : (∫⁻ x in cubicalAnnulus (n + 1) ρ R, g x) ≠ ⊤) :
    IsFiniteMeasure (surfaceEnergyMeasure ρ R g) := by
  constructor
  rw [surfaceEnergyMeasure_univ hρ hg]
  exact ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hfinite)




end

end CoarseDeGiorgi.Selection
