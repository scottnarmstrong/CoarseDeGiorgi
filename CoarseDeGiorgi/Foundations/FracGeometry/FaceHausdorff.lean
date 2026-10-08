import CoarseDeGiorgi.Foundations.FracGeometry.ChartLipschitz
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceBasics

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {n : ℕ}

theorem isometry_insertNth (i : Fin (n + 1)) (c : ℝ) :
    Isometry (fun u : Vec n => (i.insertNth (α := fun _ => ℝ) c) u) := by
  apply Isometry.of_dist_eq
  intro u v
  simp only [dist_eq_norm]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    refine (Fin.forall_iff_succAbove (P := fun j =>
      ‖((i.insertNth (α := fun _ => ℝ) c) u - (i.insertNth (α := fun _ => ℝ) c) v) j‖ ≤ ‖u - v‖) i).mpr ?_
    constructor
    · simp
    · intro j
      simpa only [Pi.sub_apply, Fin.insertNth_apply_succAbove] using norm_le_pi_norm (u - v) j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    simpa only [Pi.sub_apply, Fin.insertNth_apply_succAbove] using
      norm_le_pi_norm ((i.insertNth (α := fun _ => ℝ) c) u - (i.insertNth (α := fun _ => ℝ) c) v) (i.succAbove j)

def fullFaceCoordinates (i : Fin (n + 1)) (c : ℝ) (j : Fin (n + 1)) : Measure ℝ :=
  if j = i then Measure.dirac c else volume

instance fullFaceCoordinates_sigmaFinite (i : Fin (n + 1)) (c : ℝ) (j : Fin (n + 1)) :
    SigmaFinite (fullFaceCoordinates i c j) := by
  unfold fullFaceCoordinates
  split_ifs <;> infer_instance

theorem pi_fullFaceCoordinates (i : Fin (n + 1)) (c : ℝ) :
    Measure.pi (fullFaceCoordinates i c) = Measure.map (fun u : Vec n => (i.insertNth (α := fun _ => ℝ) c) u) volume := by
  have hp := (measurePreserving_piFinSuccAbove (fullFaceCoordinates i c) i).symm.map_eq
  have hcoords : (fun j : Fin n => fullFaceCoordinates i c (i.succAbove j)) = fun _ => volume := by
    funext j
    simp [fullFaceCoordinates]
  rw [hcoords] at hp
  simp only [fullFaceCoordinates, ite_true, Measure.dirac_prod] at hp
  rw [Measure.map_map] at hp
  · convert hp.symm using 1
    rfl
  · exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurable
  · exact measurable_prodMk_left

theorem faceMeasure_le_map_insertNth (τ : ℝ) (i : Fin (n + 1)) (positive : Bool) :
    faceMeasure τ i positive ≤ Measure.map
      (fun u : Vec n => (i.insertNth (α := fun _ => ℝ) (if positive then τ/2 else -τ/2)) u) volume := by
  classical
  let c : ℝ := if positive then τ/2 else -τ/2
  let S : Fin (n + 1) → Set ℝ := fun j => if j = i then univ else Ioo (-τ/2) (τ/2)
  have he : faceMeasure τ i positive =
      (Measure.pi (fullFaceCoordinates i c)).restrict (Set.pi univ S) := by
    rw [faceMeasure_eq_pi, Measure.restrict_pi_pi]
    congr 1
    funext j
    by_cases hji : j = i <;> simp [fullFaceCoordinates, c, hji]
  rw [he, ← pi_fullFaceCoordinates]
  exact Measure.restrict_le_self

end

end CoarseDeGiorgi.Foundations.FracGeometry
