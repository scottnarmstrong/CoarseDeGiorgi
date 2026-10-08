module

public import CoarseDeGiorgi.Foundations.FractionalSobolev.Sequence
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

def dyadicHeight (k : ℤ) : ℝ := (2 : ℝ) ^ (k : ℝ)
def dyadicLevel {X : Type*} (f : X → ℝ) (k : ℤ) : Set X := {x | dyadicHeight k < |f x|}
def dyadicBand {X : Type*} (f : X → ℝ) (k : ℤ) : Set X := dyadicLevel f k \ dyadicLevel f (k + 1)

lemma dyadicHeight_pos (k : ℤ) : 0 < dyadicHeight k := Real.rpow_pos_of_pos (by norm_num) _
lemma dyadicHeight_mono : Monotone dyadicHeight := fun i j hij =>
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.cast_le.mpr hij)
lemma dyadicHeight_add_one (k : ℤ) : dyadicHeight (k + 1) = 2 * dyadicHeight k := by
  simp only [dyadicHeight, Int.cast_add, Int.cast_one, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one, mul_comm]

lemma dyadicLevel_antitone {X : Type*} (f : X → ℝ) : Antitone (dyadicLevel f) := by
  intro i j hij x hx
  exact (dyadicHeight_mono hij).trans_lt hx

lemma dyadicLevel_measurable {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) (k : ℤ) : MeasurableSet (dyadicLevel f k) :=
  measurableSet_lt measurable_const (continuous_abs.measurable.comp hf)
lemma dyadicBand_measurable {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) (k : ℤ) : MeasurableSet (dyadicBand f k) :=
  (dyadicLevel_measurable hf k).diff (dyadicLevel_measurable hf (k + 1))

lemma mem_dyadicBand {X : Type*} {f : X → ℝ} {k : ℤ} {x : X} :
    x ∈ dyadicBand f k ↔ dyadicHeight k < |f x| ∧ |f x| ≤ dyadicHeight (k + 1) := by
  simp [dyadicBand, dyadicLevel, not_lt]

lemma dyadicBand_disjoint {X : Type*} (f : X → ℝ) : Pairwise (fun i j => Disjoint (dyadicBand f i) (dyadicBand f j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨hi, hi'⟩ := mem_dyadicBand.mp hxi
  obtain ⟨hj, hj'⟩ := mem_dyadicBand.mp hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hi'.trans (dyadicHeight_mono (by omega)))) hj
  · exact (not_lt_of_ge (hj'.trans (dyadicHeight_mono (by omega)))) hi

lemma exists_dyadicBand {X : Type*} {f : X → ℝ} {x : X} (hx : f x ≠ 0) :
    ∃ k : ℤ, x ∈ dyadicBand f k := by
  let t := Real.log |f x| / Real.log 2
  let k : ℤ := ⌈t⌉ - 1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hval : (2 : ℝ) ^ t = |f x| := by
    rw [Real.rpow_def_of_pos (by norm_num), show Real.log 2 * t = Real.log |f x| by
      dsimp [t]; field_simp]
    exact Real.exp_log (abs_pos.mpr hx)
  refine ⟨k, mem_dyadicBand.mpr ⟨?_, ?_⟩⟩
  · rw [← hval]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    dsimp [k]
    push_cast
    linarith [Int.ceil_lt_add_one t]
  · rw [← hval]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [k]
    push_cast
    linarith [Int.le_ceil t]

lemma dyadicLevel_eq_bands {X : Type*} {f : X → ℝ} {N : ℤ}
    (hN : dyadicLevel f N = ∅) (i : ℤ) :
    dyadicLevel f i = ⋃ j ∈ Finset.Ico i N, dyadicBand f j := by
  ext x
  constructor
  · intro hx
    have hz : f x ≠ 0 := by
      intro hz
      have hh := (dyadicHeight_pos i).trans hx
      simp [hz] at hh
    obtain ⟨j, hj⟩ := exists_dyadicBand hz
    refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_Ico.mpr ⟨?_, ?_⟩, hj⟩
    · by_contra h
      have hh : j + 1 ≤ i := by omega
      exact (not_lt_of_ge ((mem_dyadicBand.mp hj).2.trans (dyadicHeight_mono hh))) hx
    · by_contra h
      have hh : N ≤ j := by omega
      have hn := dyadicLevel_antitone f hh (mem_dyadicBand.mp hj).1
      rw [hN] at hn
      exact hn
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    exact dyadicLevel_antitone f (Finset.mem_Ico.mp hj).1 (mem_dyadicBand.mp hxj).1

lemma dyadicLevel_measure_eq_sum {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f)
    {N : ℤ} (hN : dyadicLevel f N = ∅) (i : ℤ) :
    volume (dyadicLevel f i) = ∑ j ∈ Finset.Ico i N, volume (dyadicBand f j) := by
  rw [dyadicLevel_eq_bands hN]
  exact measure_biUnion_finset ((dyadicBand_disjoint f).set_pairwise _) (fun j _ => dyadicBand_measurable hf j)

lemma dyadicLevel_cutoff {X : Type*} {f : X → ℝ} {M : ℝ} (hf : ∀ x, |f x| ≤ M) :
    ∃ N : ℤ, ∀ k, N ≤ k → dyadicLevel f k = ∅ := by
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hpowAll : ∀ m : ℕ, (m : ℝ) ≤ (2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ N ih =>
      rw [Nat.cast_succ, pow_succ]
      have hh : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      linarith
  have hpow := hpowAll N
  refine ⟨N, fun k hk => Set.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)⟩
  have hheight : (2 : ℝ) ^ N ≤ dyadicHeight k := by
    rw [← Real.rpow_natCast]
    exact dyadicHeight_mono hk
  exact (not_lt_of_ge ((hf x).trans (hN.le.trans (hpow.trans hheight)))) hx

lemma dyadicLevel_measure_bound {n : ℕ} {f : Vec n → ℝ} (hf : HasCompactSupport f) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ k, volume (dyadicLevel f k) ≤ M := by
  refine ⟨volume (tsupport f), hf.measure_lt_top.ne, fun k => measure_mono ?_⟩
  intro x hx
  apply subset_closure
  change f x ≠ 0
  intro hz
  have hh := (dyadicHeight_pos k).trans hx
  simp [hz] at hh

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
