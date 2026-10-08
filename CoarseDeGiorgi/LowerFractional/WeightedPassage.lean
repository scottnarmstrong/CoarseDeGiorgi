module

public import CoarseDeGiorgi.LowerFractional.FractionalDifference
public import CoarseDeGiorgi.Weighted.Truncation.Truncate

/-! Passage from bounded members to the weighted completion.
This uses the proved weighted truncation calculus and Fatou; the eventual
pointwise identity avoids requiring completeness of a separately chosen
fractional-space carrier. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- Symmetric truncation is pointwise bounded by its level. -/
theorem norm_truncate_le {N : ℝ} (hN : 0 ≤ N) (v : ℝ) :
    ‖Weighted.truncate N v‖ ≤ N := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (neg_le_self hN) (min_le_right _ _)

/-- Increasing truncations are eventually identical to a fixed scalar. -/
theorem truncate_tendsto (v : ℝ) :
    Tendsto (fun n : ℕ => Weighted.truncate (n + 1) v) atTop (𝓝 v) := by
  have hev : ∀ᶠ n : ℕ in atTop, |v| ≤ (n : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt |v|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with n hn
  have h := abs_le.mp hn
  simp only [Weighted.truncate, min_eq_left h.2, max_eq_right h.1]

/-- Bounded truncations retain membership and have no larger weighted energy. -/
theorem weighted_truncation_approximation {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) (r : ℝ) :
    ∃ f : ℕ → Vec d → ℝ, ∃ F : ℕ → Vec d → Vec d,
      (∀ n, MemH1a a V (f n) (F n)) ∧
      (∀ n, MemLp (f n) (ENNReal.ofReal r) (volume.restrict V)) ∧
      (∀ n, weightedEnergy a V (F n) ≤ weightedEnergy a V G) ∧
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (w x))) := by
  let : IsFiniteMeasure (volume.restrict V) :=
    hV.isBoundedDomain.isFiniteMeasure_restrict_volume
  let f : ℕ → Vec d → ℝ := fun n x => Weighted.truncate (n + 1) (w x)
  let F : ℕ → Vec d → Vec d := fun n => {x | |w x| < (n : ℝ) + 1}.indicator G
  have hf (n : ℕ) : MemH1a a V (f n) (F n) :=
    Weighted.MemH1a.truncation hV hne ha hw (by positivity)
  refine ⟨f, F, hf, ?_, ?_, ?_⟩
  · intro n
    exact MemLp.of_bound (hf n).1 (n + 1)
      (Eventually.of_forall fun x => norm_truncate_le (by positivity) (w x))
  · intro n
    exact Weighted.energy_truncate_le ha w G (n + 1)
  · intro x
    exact truncate_tendsto (w x)

/-- A uniform bounded-member energy estimate extends to every H1a pair.
The premise is a proved-stage input for assembly, not an additional premise
of any source theorem. -/
theorem fractional_bound_of_bounded_estimate {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {a : CoeffField d} {α r : ℝ} {K : ℝ≥0∞}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (hr : 0 < r)
    (hbounded : ∀ (w : Vec d → ℝ) (G : Vec d → Vec d),
      MemH1a a V w G → MemLp w (ENNReal.ofReal r) (volume.restrict V) →
        fracSeminorm V α r w ≤ K * (weightedEnergy a V G) ^ (1 / 2 : ℝ))
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : MemH1a a V w G) :
    fracSeminorm V α r w ≤ K * (weightedEnergy a V G) ^ (1 / 2 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict V) :=
    hV.isBoundedDomain.isFiniteMeasure_restrict_volume
  obtain ⟨f, F, hf, hfLp, hE, ht⟩ := weighted_truncation_approximation hV hne ha hw r
  apply fracSeminorm_le_of_ae_tendsto hr (fun n => (hf n).1) hw.1 ?_
    (Eventually.of_forall ht)
  exact Eventually.of_forall fun n => (hbounded (f n) (F n) (hf n) (hfLp n)).trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (z := (1 / 2 : ℝ)) (hE n) (by norm_num)))


end CoarseDeGiorgi.LowerFractional
