module

public import CoarseDeGiorgi.Sharpness.LineEquation.Geometry
public import CoarseDeGiorgi.Foundations.Euclid.Basic
public import CoarseDeGiorgi.Statements.OriginCube
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators

namespace CoarseDeGiorgi.Sharpness

lemma lineRadius_nonneg {d : ℕ} (x : Vec d) : 0 ≤ transverseNorm x :=
  euclideanNorm_nonneg _

lemma lineRadius_continuous {d : ℕ} : Continuous (transverseNorm (d := d)) := by
  change Continuous (CoarseDeGiorgi.Foundations.Euclid.eNorm2 ∘ transversePart)
  exact CoarseDeGiorgi.Foundations.Euclid.continuous_eNorm2.comp
    transversePart_contDiff.continuous

lemma abs_transverse_coordinate_le {d : ℕ} (x : Vec d) (i : Fin d) (hi : i.val ≠ 0) :
    |x i| ≤ transverseNorm x := by
  have h := (norm_le_pi_norm (transversePart x) i).trans
    (CoarseDeGiorgi.Foundations.Euclid.norm_le_eNorm2 (transversePart x))
  simpa [transversePart, hi, Real.norm_eq_abs, transverseNorm, euclideanNorm,
    CoarseDeGiorgi.Foundations.Euclid.eNorm2] using h

/-- The singular line is null already in every dimension at least two. -/
lemma lineRadius_pos_ae {d : ℕ} (hd : 2 ≤ d) :
    ∀ᵐ x : Vec d ∂volume, 0 < transverseNorm x := by
  let μ : Fin d → Measure ℝ := fun _ => volume
  have hcoord : ∀ᵐ x : Vec d ∂volume, x ⟨1, by omega⟩ ≠ (0 : ℝ) := by
    simpa only [MeasureTheory.volume_pi] using
      (Measure.ae_eval_ne μ (⟨1, by omega⟩ : Fin d) (0 : ℝ))
  filter_upwards [hcoord] with x hx
  have hb := abs_transverse_coordinate_le x (⟨1, by omega⟩ : Fin d) (by simp)
  exact lt_of_lt_of_le (abs_pos.mpr hx) hb

/-- A box containing the transverse annulus inside the unit cube. -/
def lineAnnulusBox {d : ℕ} (ε : ℝ) : Set (Vec d) :=
  Icc (fun i => if i.val = 0 then -1 else -(2 * ε))
    (fun i => if i.val = 0 then 1 else 2 * ε)

lemma mem_lineAnnulusBox {d : ℕ} {ε : ℝ} {x : Vec d}
    (hx : x ∈ CoarseDeGiorgi.originCube 1) (hr : transverseNorm x ≤ 2 * ε) :
    x ∈ lineAnnulusBox ε := by
  constructor <;> intro i
  · by_cases hi : i.val = 0
    · simp only [hi, ite_true]
      have h := (hx i).1
      norm_num at h
      linarith
    · simp only [hi, ite_false]
      exact (abs_le.mp ((abs_transverse_coordinate_le x i hi).trans hr)).1
  · by_cases hi : i.val = 0
    · simp only [hi, ite_true]
      have h := (hx i).2
      norm_num at h
      linarith
    · simp only [hi, ite_false]
      exact (abs_le.mp ((abs_transverse_coordinate_le x i hi).trans hr)).2

lemma lineAnnulusBox_measurable {d : ℕ} (ε : ℝ) :
    MeasurableSet (lineAnnulusBox (d := d) ε) := measurableSet_Icc

lemma lineAnnulusBox_volume {d : ℕ} [NeZero d] {ε : ℝ} (hε : 0 ≤ ε) :
    (volume (lineAnnulusBox (d := d) ε)).toReal = 2 * (4 * ε) ^ (d - 1) := by
  rw [lineAnnulusBox, Real.volume_Icc_pi_toReal]
  · have heq : (fun i : Fin d =>
        (if i.val = 0 then (1 : ℝ) else 2 * ε) -
          (if i.val = 0 then -1 else -(2 * ε))) =
        (fun i => if i = 0 then 2 else 4 * ε) := by
      funext i
      by_cases hi : i = 0
      · subst i
        norm_num
      · have hv : i.val ≠ 0 := fun hv => hi (Fin.ext hv)
        simp [hi, hv]
        ring
    rw [heq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin d))]
    simp only [ite_true]
    have herase : (∏ i ∈ Finset.univ.erase (0 : Fin d),
        if i = 0 then (2 : ℝ) else 4 * ε) = (4 * ε) ^ (d - 1) := by
      calc
        _ = ∏ _i ∈ Finset.univ.erase (0 : Fin d), 4 * ε := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [Finset.ne_of_mem_erase hi]
        _ = _ := by simp
    rw [herase]
  · intro i
    dsimp
    split_ifs <;> linarith

lemma lineAnnulusBox_volume_lt_top {d : ℕ} (ε : ℝ) :
    volume (lineAnnulusBox (d := d) ε) < ⊤ :=
  isCompact_Icc.measure_lt_top

end CoarseDeGiorgi.Sharpness
