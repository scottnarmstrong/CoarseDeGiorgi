import CoarseDeGiorgi.Whitney.Harmonic.Glue
import CoarseDeGiorgi.Selection.Coarea
import CoarseDeGiorgi.Statements.CubeSurface

/-! The face measures live on the cube surface; boundedness of Lipschitz boundary data. -/

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem ae_cubeFace_mem_surface {n : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin (n + 1)) (b : Bool) :
    ∀ᵐ x ∂CoarseDeGiorgi.cubeFaceMeasure τ i b, x ∈ CoarseDeGiorgi.cubeSurface (d := n + 1) τ := by
  rw [Selection.cubeFaceMeasure_eq_map]
  have hmeas : Measurable (fun u : Vec n => i.insertNth (α := fun _ => ℝ)
      (if b then τ / 2 else -τ / 2) u) :=
    (Selection.measurable_insertNth i).comp (measurable_prodMk_left)
  have hS : MeasurableSet {y : Vec (n + 1) | ‖y‖ = τ / 2} :=
    measurableSet_eq_fun measurable_norm measurable_const
  change ∀ᵐ x ∂_, ‖x‖ = τ / 2
  rw [ae_map_iff hmeas.aemeasurable hS]
  filter_upwards [ae_restrict_mem (Selection.measurableSet_faceBox n τ)] with u hu
  have hu' : ∀ j, |u j| < τ / 2 := fun j => by
    have := hu j (mem_univ j)
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have hc : |(if b then τ / 2 else -τ / 2)| = τ / 2 := by
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [show -τ / 2 = -(τ / 2) by ring, abs_neg, abs_of_nonneg (by linarith)]
    · simp only [ite_true]
      exact abs_of_nonneg (by linarith)
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro k
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · rw [Real.norm_eq_abs, Fin.insertNth_apply_same, hc]
    · rw [Real.norm_eq_abs, Fin.insertNth_apply_succAbove]
      exact (hu' j).le
  · have := norm_le_pi_norm (i.insertNth (α := fun _ => ℝ) (if b then τ / 2 else -τ / 2) u) i
    rw [Fin.insertNth_apply_same, Real.norm_eq_abs, hc] at this
    exact this

end CoarseDeGiorgi.Whitney.Harmonic
