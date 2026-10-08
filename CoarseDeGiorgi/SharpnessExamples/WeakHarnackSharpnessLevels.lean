module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessPolar
public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Power means of simplex averages from a splitting of the majorant

A nonnegative field `W₁ + W₂`, with `W₁` integrable and `W₂` bounded, has simplex power means
controlled by `(card)^{q-1} (∫ W₁)^q + ∫ W₂^q`.
-/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem volumeAverage_eq_average {d : ℕ} (V : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage V f = ⨍ x in V, f x := by
  unfold volumeAverage
  rw [average_eq, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]

theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {q : ℝ} (hq : 1 ≤ q) : ∑ i ∈ s, a i ^ q ≤ (∑ i ∈ s, a i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Real.zero_rpow (by linarith)]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    calc a i ^ q + ∑ j ∈ s, a j ^ q ≤ a i ^ q + (∑ j ∈ s, a j) ^ q := by linarith
      _ ≤ _ := Real.add_rpow_le_rpow_add (ha i) (Finset.sum_nonneg (fun j _ => ha j)) hq

theorem add_rpow_le_two_pow_mul {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 1 ≤ q) :
    (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) := by
  have h2 : (a + b) ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have hm : 0 ≤ max a b := le_trans ha (le_max_left _ _)
  calc (a + b) ^ q ≤ (2 * max a b) ^ q :=
        Real.rpow_le_rpow (add_nonneg ha hb) h2 (by linarith)
    _ = 2 ^ q * max a b ^ q := Real.mul_rpow (by norm_num) hm
    _ ≤ 2 ^ q * (a ^ q + b ^ q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]; have := Real.rpow_nonneg ha q; linarith
        · rw [max_eq_left h]; have := Real.rpow_nonneg hb q; linarith

theorem simplex_jensen {d : ℕ} (k : ℕ) (η : SimplexIndex d k) {q : ℝ} (hq : 1 ≤ q)
    {f : Vec d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : IntegrableOn f (originCube 1))
    (hfq : IntegrableOn (fun x => f x ^ q) (originCube 1)) :
    volumeAverage (simplexCell k η) f ^ q ≤
      volumeAverage (simplexCell k η) (fun x => f x ^ q) := by
  have hsub := CoarseDeGiorgi.simplexCell_subset_originCube k η
  have hfin : volume (simplexCell k η) ≠ ⊤ :=
    (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
  have hpos : volume (simplexCell k η) ≠ 0 := by
    intro h0
    have := Assembly.ClassicalMomentsImpl.simplexCell_volume_real (d := d) k η
    rw [h0] at this
    simp only [ENNReal.toReal_zero] at this
    have hN : (0 : ℝ) < ((triangulation (d := d) k).card : ℝ) :=
      Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)
    exact (inv_pos.mpr hN).ne this
  have : IsFiniteMeasure (volume.restrict (simplexCell k η)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have : NeZero (volume.restrict (simplexCell k η)) :=
    ⟨fun h => hpos (Measure.restrict_eq_zero.mp h)⟩
  rw [volumeAverage_eq_average, volumeAverage_eq_average]
  have := (convexOn_rpow hq).map_average_le (μ := volume.restrict (simplexCell k η))
    (f := f) (continuousOn_id.rpow_const (fun _ _ => Or.inr (by linarith)))
    isClosed_Ici (Filter.Eventually.of_forall (fun x => hf0 x))
    (hf.mono_set hsub) (hfq.mono_set hsub)
  simpa using this

theorem level_power_mean_le {d : ℕ} (k : ℕ) {q : ℝ} (hq : 1 ≤ q) (W1 W2 : Vec d → ℝ)
    (h1 : ∀ x, 0 ≤ W1 x) (h2 : ∀ x, 0 ≤ W2 x)
    (hW1 : IntegrableOn W1 (originCube 1)) (hW2 : IntegrableOn W2 (originCube 1))
    (hW2q : IntegrableOn (fun x => W2 x ^ q) (originCube 1)) :
    ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow (volumeAverage (simplexCell k η) (fun x => W1 x + W2 x)) q) /
      ((triangulation (d := d) k).card : ℝ) ≤
    2 ^ q * (((triangulation (d := d) k).card : ℝ) ^ (q - 1) *
        (∫ x in originCube 1, W1 x) ^ q + ∫ x in originCube 1, W2 x ^ q) := by
  classical
  set N : ℝ := ((triangulation (d := d) k).card : ℝ) with hN
  have hNpos : 0 < N := Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)
  have hnn : ∀ (V : Set (Vec d)) (f : Vec d → ℝ), (∀ x, 0 ≤ f x) → 0 ≤ volumeAverage V f := by
    intro V f hf
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hf)
  let T := (triangulation (d := d) k).attach
  let a : _ → ℝ := fun η => volumeAverage (simplexCell k η) W1
  let b : _ → ℝ := fun η => volumeAverage (simplexCell k η) W2
  have hsubη := fun η => CoarseDeGiorgi.simplexCell_subset_originCube (d := d) k η
  have hadd : ∀ η, volumeAverage (simplexCell k η) (fun x => W1 x + W2 x) = a η + b η := by
    intro η
    exact volumeAverage_add (hW1.mono_set (hsubη η)) (hW2.mono_set (hsubη η))
  have ha0 : ∀ η, 0 ≤ a η := fun η => hnn _ _ h1
  have hb0 : ∀ η, 0 ≤ b η := fun η => hnn _ _ h2
  have hsumA : T.sum a = N * ∫ x in originCube 1, W1 x := by
    have := Assembly.ClassicalMomentsImpl.partition_average (d := d) k hW1
    change T.sum a / N = _ at this
    rw [← this]; field_simp
  have hsumB : T.sum (fun η => volumeAverage (simplexCell k η) (fun x => W2 x ^ q)) =
      N * ∫ x in originCube 1, W2 x ^ q := by
    have := Assembly.ClassicalMomentsImpl.partition_average (d := d) k hW2q
    change T.sum (fun η => volumeAverage (simplexCell k η) (fun x => W2 x ^ q)) / N = _ at this
    rw [← this]; field_simp
  have hA : T.sum (fun η => a η ^ q) ≤ N ^ q * (∫ x in originCube 1, W1 x) ^ q := by
    calc T.sum (fun η => a η ^ q) ≤ (T.sum a) ^ q := sum_rpow_le_rpow_sum T a ha0 hq
      _ = _ := by rw [hsumA, Real.mul_rpow hNpos.le (integral_nonneg h1)]
  have hB : T.sum (fun η => b η ^ q) ≤ N * ∫ x in originCube 1, W2 x ^ q := by
    rw [← hsumB]
    exact Finset.sum_le_sum (fun η _ => simplex_jensen k η hq h2 hW2 hW2q)
  have hmain : T.sum (fun η => Real.rpow (volumeAverage (simplexCell k η) (fun x => W1 x + W2 x)) q) ≤
      2 ^ q * (T.sum (fun η => a η ^ q) + T.sum (fun η => b η ^ q)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun η _ => ?_)
    rw [hadd η]
    exact add_rpow_le_two_pow_mul (ha0 η) (hb0 η) hq
  rw [div_le_iff₀ hNpos]
  calc _ ≤ 2 ^ q * (N ^ q * (∫ x in originCube 1, W1 x) ^ q + N * ∫ x in originCube 1, W2 x ^ q) :=
        hmain.trans (mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity))
    _ = _ := by
        rw [Real.rpow_sub_one hNpos.ne']
        field_simp

end

end CoarseDeGiorgi.SharpnessExamples
