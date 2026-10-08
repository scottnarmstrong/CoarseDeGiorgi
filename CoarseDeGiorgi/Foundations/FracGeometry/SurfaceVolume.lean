module

public import CoarseDeGiorgi.Foundations.FracGeometry.FaceHausdorff
public import CoarseDeGiorgi.Foundations.FracGeometry.Cutoff

@[expose] public section

namespace CoarseDeGiorgi.Foundations.FracGeometry
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
variable {d : ℕ}

theorem faceMeasure_univ_le_one {τ : ℝ} (hτ : τ ≤ 1) (i : Fin d) (pos : Bool) :
    faceMeasure τ i pos univ ≤ 1 := by
  classical
  rw [faceMeasure_eq_pi]
  let μ : Fin d → Measure ℝ := fun j => if j = i then Measure.dirac (if pos then τ/2 else -τ/2)
    else volume.restrict (Ioo (-τ/2) (τ/2))
  have : ∀ j, IsFiniteMeasure (μ j) := fun j => by dsimp only [μ]; split_ifs <;> infer_instance
  change Measure.pi μ univ ≤ 1
  rw [Measure.pi_univ]
  apply Finset.prod_le_one
  intro j hj
  dsimp only [μ]
  by_cases hji : j = i
  · rw [ite_eq_left hji]; simp
  · rw [ite_eq_right hji]
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    have he : τ / 2 - -τ / 2 = τ := by ring
    rw [he]
    exact (ENNReal.ofReal_le_ofReal hτ).trans_eq (by norm_num)

theorem surfaceMeasure_univ_le {τ : ℝ} (hτ : τ ≤ 1) :
    surfaceMeasure (d := d) τ univ ≤ (2 * d : ℝ≥0∞) := by
  rw [surfaceMeasure_eq_sum_faceMeasure]
  simp only [Measure.finsetSum_apply]
  calc
    _ ≤ ∑ _i : Fin d, ∑ _pos : Bool, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun pos _ => faceMeasure_univ_le_one hτ i pos
    _ = _ := by simp; ring

end
end CoarseDeGiorgi.Foundations.FracGeometry
