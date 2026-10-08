import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Hom.CompleteLattice

namespace CoarseDeGiorgi.Selection

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Nonnegative Lᵖ quantity, kept in ENNReal to handle zero and infinite controls honestly. -/
def powerNorm (r : ℝ) (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ τ, (f τ) ^ r ∂μ) ^ (1 / r)

/-- Maximum of abstract cell responses over a specified radius incidence set.
The empty maximum is zero, as in `e.boundary.maxima`. -/
def sampledMaximum {Cell : Type*} (cells : Finset Cell) (weight : Cell → ℝ≥0∞)
    (incidence : Cell → Set ℝ) (τ : ℝ) : ℝ≥0∞ := by
  classical
  exact cells.sup (fun c => (incidence c).indicator (fun _ => weight c) τ)

theorem sampledMaximum_measurable {Cell : Type*} (cells : Finset Cell)
    (weight : Cell → ℝ≥0∞) (incidence : Cell → Set ℝ)
    (hinc : ∀ c ∈ cells, MeasurableSet (incidence c)) :
    Measurable (sampledMaximum cells weight incidence) := by
  classical
  unfold sampledMaximum
  induction cells using Finset.induction_on with
  | empty => simp
  | @insert c s hc ih =>
    simp only [Finset.sup_insert]
    exact (measurable_const.indicator (hinc c (Finset.mem_insert_self _ _))).sup
      (ih (fun c hc => hinc c (Finset.mem_insert_of_mem hc)))

/-- The maximum-to-sum argument; no response theorem is used. -/
theorem sampledMaximum_power_le_sum {Cell : Type*} (cells : Finset Cell)
    (weight : Cell → ℝ≥0∞) (incidence : Cell → Set ℝ) {p : ℝ} (hp : 0 < p) (τ : ℝ) :
    (sampledMaximum cells weight incidence τ) ^ p ≤
      ∑ c ∈ cells, (incidence c).indicator (fun _ => weight c ^ p) τ := by
  classical
  by_cases hempty : cells = ∅
  · subst cells
    simp [sampledMaximum, ENNReal.zero_rpow_of_pos hp]
  · obtain ⟨c, hc, heq⟩ := cells.exists_mem_eq_sup (Finset.nonempty_iff_ne_empty.mpr hempty)
      (fun c => (incidence c).indicator (fun _ => weight c) τ)
    change (cells.sup _) ^ p ≤ _
    rw [heq]
    have he : ((incidence c).indicator (fun _ => weight c) τ) ^ p =
        (incidence c).indicator (fun _ => weight c ^ p) τ := by
      by_cases hτ : τ ∈ incidence c <;> simp [hτ, ENNReal.zero_rpow_of_pos hp]
    rw [he]
    exact Finset.single_le_sum (f := fun c => (incidence c).indicator (fun _ => weight c ^ p) τ)
      (fun _ _ => bot_le) hc

/-- The width-of-incidence estimate in the proof of Lemma `l.radius.averages`, for arbitrary
nonnegative cell data. -/
theorem sampledMaximum_integral_le {Cell : Type*} (cells : Finset Cell)
    (weight : Cell → ℝ≥0∞) (incidence : Cell → Set ℝ)
    (hinc : ∀ c ∈ cells, MeasurableSet (incidence c)) {μ : Measure ℝ}
    {p : ℝ} (hp : 0 < p) {width : ℝ≥0∞}
    (hwidth : ∀ c ∈ cells, μ (incidence c) ≤ width) :
    (∫⁻ τ, (sampledMaximum cells weight incidence τ) ^ p ∂μ) ≤
      width * ∑ c ∈ cells, weight c ^ p := by
  calc
    _ ≤ ∫⁻ τ, ∑ c ∈ cells, (incidence c).indicator (fun _ => weight c ^ p) τ ∂μ :=
      lintegral_mono (sampledMaximum_power_le_sum cells weight incidence hp)
    _ = ∑ c ∈ cells, weight c ^ p * μ (incidence c) := by
      rw [lintegral_finsetSum _ (fun c hc => measurable_const.indicator (hinc c hc))]
      apply Finset.sum_congr rfl
      intro c hc
      exact lintegral_indicator_const (hinc c hc) _
    _ ≤ ∑ c ∈ cells, weight c ^ p * width :=
      Finset.sum_le_sum (fun c hc => by gcongr; exact hwidth c hc)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- A radius-incidence interval with center `a` and half-width `h` has volume `2h`.
This is the abstract geometric input to the sampling estimate. -/
theorem incidence_measure_le {E : Set ℝ} {a h : ℝ} (hE : E ⊆ Icc (a - h) (a + h)) :
    volume E ≤ ENNReal.ofReal (2 * h) := by
  apply (measure_mono hE).trans_eq
  rw [Real.volume_Icc]
  congr 1
  ring

/-- Finite Minkowski for nonnegative functions. -/
theorem powerNorm_sum_le {ι : Type*} (s : Finset ι) {r : ℝ} (hr : 1 ≤ r)
    (μ : Measure ℝ) (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    powerNorm r μ (fun τ => ∑ i ∈ s, f i τ) ≤ ∑ i ∈ s, powerNorm r μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hr' : 0 < r := lt_of_lt_of_le zero_lt_one hr
    simp [powerNorm, ENNReal.zero_rpow_of_pos hr', hr']
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (ENNReal.lintegral_Lp_add_le (μ := μ)
      (hf i (Finset.mem_insert_self _ _)).aemeasurable
      (Finset.measurable_sum _ (fun j hj => hf j (Finset.mem_insert_of_mem hj))).aemeasurable hr).trans
      (add_le_add le_rfl (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))


end

end CoarseDeGiorgi.Selection
