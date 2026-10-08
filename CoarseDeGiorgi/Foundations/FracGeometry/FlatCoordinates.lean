module

public import CoarseDeGiorgi.Foundations.FracGeometry.TranslationEnergy

@[expose] public section

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

variable {n : ℕ}

/-- Place the slicing coordinate first and the tangential coordinates afterwards. -/
def flatJoin (l : ℝ) (x : Vec n) : Vec (n + 1) := Fin.cons l x

theorem volume_preserving_flatJoin :
    MeasurePreserving (fun lx : ℝ × Vec n => flatJoin lx.1 lx.2)
      (volume.prod volume) volume := by
  convert (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm using 1
  ext lx i
  simp [flatJoin, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

end

end CoarseDeGiorgi.Foundations.FracGeometry
