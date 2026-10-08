import CoarseDeGiorgi.Foundations.FracGeometry.Defs

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem prod_finsetSum_left {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (s : Finset ι) (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (ν : Measure Y) [IsFiniteMeasure ν] :
    (∑ i ∈ s, μ i).prod ν = ∑ i ∈ s, (μ i).prod ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Measure.zero_prod]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Measure.add_prod, ih, Finset.sum_insert hi]

private theorem prod_finsetSum_right {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Finset ι)
    (ν : ι → Measure Y) [∀ i, IsFiniteMeasure (ν i)] :
    μ.prod (∑ i ∈ s, ν i) = ∑ i ∈ s, μ.prod (ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Measure.prod_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Measure.prod_add, ih, Finset.sum_insert hi]

variable {d : ℕ}

/-- The product surface measure includes every ordered pair of faces. -/
theorem surfaceMeasure_prod_eq_sum_faces (τ : ℝ) :
    (surfaceMeasure (d := d) τ).prod (surfaceMeasure τ) =
      ∑ i : Fin d, ∑ positive : Bool, ∑ j : Fin d, ∑ positive' : Bool,
        (faceMeasure τ i positive).prod (faceMeasure τ j positive') := by
  simp_rw [surfaceMeasure_eq_sum_faceMeasure, prod_finsetSum_left, prod_finsetSum_right]

/-- This expansion retains near pairs lying on different faces. -/
theorem lintegral_surfaceMeasure_prod (τ : ℝ) (f : Vec d × Vec d → ℝ≥0∞) :
    (∫⁻ xy, f xy ∂((surfaceMeasure τ).prod (surfaceMeasure τ))) =
      ∑ i : Fin d, ∑ positive : Bool, ∑ j : Fin d, ∑ positive' : Bool,
        ∫⁻ xy, f xy ∂((faceMeasure τ i positive).prod (faceMeasure τ j positive')) := by
  rw [surfaceMeasure_prod_eq_sum_faces]
  simp_rw [lintegral_finsetSum_measure]

end

end CoarseDeGiorgi.Foundations.FracGeometry
