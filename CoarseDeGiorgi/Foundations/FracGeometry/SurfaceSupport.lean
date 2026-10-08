import CoarseDeGiorgi.Foundations.FracGeometry.FaceHausdorff
import CoarseDeGiorgi.Foundations.FracGeometry.Cutoff

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

theorem faceMeasure_ae_surface {τ : ℝ} (hτ : 0 ≤ τ) (i : Fin d) (pos : Bool) :
    ∀ᵐ x ∂faceMeasure τ i pos, x ∈ cubeSurface τ := by
  rw [faceMeasure_eq_pi]
  let μ : Fin d → Measure ℝ := fun j => if j = i then
    Measure.dirac (if pos then τ / 2 else -τ / 2) else volume.restrict (Ioo (-τ / 2) (τ / 2))
  have : ∀ j, IsFiniteMeasure (μ j) := fun j => by dsimp only [μ]; split_ifs <;> infer_instance
  have hj : ∀ j, ∀ᵐ a ∂μ j, |a| ≤ τ / 2 ∧ (j = i → a = if pos then τ / 2 else -τ / 2) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [μ, ite_eq_left rfl, ae_dirac_eq]
      cases pos <;> simp [abs_div, abs_of_nonneg hτ]
    · have he := ae_restrict_mem (s := Ioo (-τ / 2) (τ / 2)) (μ := (volume : Measure ℝ)) measurableSet_Ioo
      simp only [μ, ite_eq_right hji]
      filter_upwards [he] with a ha
      exact ⟨abs_le.mpr ⟨by simpa only [neg_div] using ha.1.le, ha.2.le⟩, fun h => (hji h).elim⟩
  have hall := (Filter.eventually_all.2 fun j => Measure.tendsto_eval_ae_ae.eventually (hj j))
  filter_upwards [hall] with x hx
  simp only [Function.eval] at hx
  change ‖x‖ = τ / 2
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (div_nonneg hτ (by norm_num))).mpr fun j => by
      simpa only [Real.norm_eq_abs] using (hx j).1
  · have hi := norm_le_pi_norm x i
    rw [(hx i).2 rfl, Real.norm_eq_abs] at hi
    cases pos <;> simpa [abs_div, abs_of_nonneg hτ] using hi

theorem surfaceMeasure_ae_surface {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᵐ x ∂surfaceMeasure (d := d) τ, x ∈ cubeSurface τ := by
  rw [surfaceMeasure_eq_sum_faceMeasure]
  apply ae_finsetSum_measure_iff.mpr
  intro i hi
  apply ae_finsetSum_measure_iff.mpr
  intro pos hp
  exact faceMeasure_ae_surface hτ i pos

end

end CoarseDeGiorgi.Foundations.FracGeometry
