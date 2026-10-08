module

public import CoarseDeGiorgi.Foundations.Reconstruction.ReconstructionEstimates
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # A common linear action for the block norm and its translation difference -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section
variable {d : ℕ}

def reconstructionAction (u : Option (Vec d)) (f : Vec d → ℝ) : Vec d → ℝ :=
  match u with | none => f | some u => fun x => f (x + u) - f x

def reconstructionModulus (h : ℝ) (u : Option (Vec d)) : ℝ :=
  match u with | none => 1 | some u => min 1 (euclidNorm u / h)

theorem reconstructionAction_sub (u : Option (Vec d)) (f g : Vec d → ℝ) :
    reconstructionAction u (fun x => f x - g x) =
      fun x => reconstructionAction u f x - reconstructionAction u g x := by
  cases u with
  | none => rfl
  | some u => funext x; dsimp only [reconstructionAction]; ring

theorem reconstructionAction_measurable (u : Option (Vec d)) {f : Vec d → ℝ} (hf : Measurable f) :
    Measurable (reconstructionAction u f) := by
  cases u with
  | none => exact hf
  | some u => exact (hf.comp (measurable_id.add_const u)).sub hf

theorem reconstructionAction_bound (u : Option (Vec d)) (h : ℝ) (F : Vec d → ℝ)
    (p : ℝ≥0∞) (μ : Measure (Vec d)) {C : ℝ≥0∞}
    (h0 : eLpNorm F p μ ≤ C)
    (h1 : ∀ v, eLpNorm (fun x => F (x + v) - F x) p μ ≤ 2 * ENNReal.ofReal (min 1 (euclidNorm v / h)) * C) :
    eLpNorm (reconstructionAction u F) p μ ≤ 2 * ENNReal.ofReal (reconstructionModulus h u) * C := by
  cases u with
  | none =>
    simp only [reconstructionAction, reconstructionModulus, ENNReal.ofReal_one, mul_one]
    exact h0.trans (by calc _ = 1 * C := (one_mul _).symm
                           _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) bot_le)
  | some u => exact h1 u

/-- A finite telescope bounded term by term stays below the full nonnegative tail. -/
theorem eLpNorm_telescope_tail_le (j : ℕ) (T : ℕ → Vec d → ℝ) (F : Vec d → ℝ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (μ : Measure (Vec d)) (a : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hbase : eLpNorm (T j) p μ ≤ C * a j)
    (hstep : ∀ k, j ≤ k → eLpNorm (fun x => T (k + 1) x - T k x) p μ ≤ C * a (k + 1))
    (hm : ∀ k, AEStronglyMeasurable (T k) μ)
    (hlim : ∀ x, Tendsto (fun k => T k x) atTop (𝓝 (F x))) :
    eLpNorm F p μ ≤ C * ∑' k, if j ≤ k then a k else 0 := by
  have hfinite (n : ℕ) : eLpNorm (T (j + n)) p μ ≤ C * ∑ k ∈ Finset.range (n + 1), a (j + k) := by
    induction n with
    | zero => simpa only [Nat.zero_add, add_zero, Finset.range_one, Finset.sum_singleton] using hbase
    | succ n ih =>
      have heq : T (j + (n + 1)) = fun x => T (j + n) x + (T (j + n + 1) x - T (j + n) x) := by
        funext x; rw [Nat.add_assoc]; ring
      rw [heq]
      calc
        _ ≤ eLpNorm (T (j + n)) p μ + eLpNorm (fun x => T (j + n + 1) x - T (j + n) x) p μ := eLpNorm_add_le hp
        _ ≤ C * (∑ k ∈ Finset.range (n + 1), a (j + k)) + C * a (j + n + 1) :=
          add_le_add ih (hstep (j + n) (Nat.le_add_right _ _))
        _ = _ := by rw [Finset.sum_range_succ (fun k => a (j + k)) (n + 1), mul_add, Nat.add_assoc]
  have htail : (∑' n, a (j + n)) ≤ ∑' k, if j ≤ k then a k else 0 := by
    simpa only [ite_eq_left (Nat.le_add_right j _)] using
      ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => j + n) (fun _ _ h => Nat.add_left_cancel h)
        (fun k => if j ≤ k then a k else 0)
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (Eventually.of_forall fun n => (hfinite n).trans
      (mul_le_mul_of_nonneg_left ((ENNReal.sum_le_tsum _).trans htail) bot_le))
    (fun n => hm (j + n))
    (aestronglyMeasurable_of_tendsto_ae atTop hm (ae_of_all _ hlim))
  exact ae_of_all _ fun x => (hlim x).comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat j)

end
end CoarseDeGiorgi.Foundations.Reconstruction
