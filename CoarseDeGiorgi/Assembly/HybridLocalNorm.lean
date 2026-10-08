module

public import CoarseDeGiorgi.LowerFractional.CubeDomain
public import CoarseDeGiorgi.Foundations.FracGeometry.Defs

@[expose] public section

namespace CoarseDeGiorgi.Assembly

open Homogenization MeasureTheory CoarseDeGiorgi.LowerFractional
open scoped ENNReal

/-- The mean estimate supplies the local Lʳ finiteness needed by localization. -/
theorem hybrid_auxiliary_norm_finite {d : ℕ} [NeZero d] {α r : ℝ}
    (hr : 1 ≤ r) (hα : 0 ≤ α) (m : ℤ) (z : Fin d → ℤ) {w : Vec d → ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict (auxCube m z)))
    (hsemi : fracSeminorm (auxCube m z) α r w < ⊤) :
    fracNorm (auxCube m z) α r w < ⊤ := by
  obtain ⟨C, _, hbound⟩ := fractional_mean_norm_auxCube (d := d) hr hα
  have hvol : volume (auxCube m z) ≠ ⊤ := by
    simpa only [← Foundations.Reconstruction.auxCube_eq_statement] using
      Foundations.Reconstruction.volume_auxCube_ne_top m z
  have hmass : eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) < ⊤ :=
    (hbound m z w hw).trans_lt (by finiteness)
  have hr0 := zero_lt_one.trans_le hr
  unfold fracNorm
  simp only [ENNReal.rpow_eq_pow]
  finiteness

/-- A finite per-cube energy bound discharges the finiteness premise above. -/
theorem hybrid_auxiliary_norm_finite_of_energy_bound {d : ℕ} [NeZero d] {α r : ℝ}
    (hr : 1 ≤ r) (hα : 0 ≤ α) (m : ℤ) (z : Fin d → ℤ)
    {w : Vec d → ℝ} {L E : ℝ≥0∞}
    (hw : AEStronglyMeasurable w (volume.restrict (auxCube m z)))
    (hL : L ≠ ⊤) (hE : E ≠ ⊤)
    (hbound : fracSeminorm (auxCube m z) α r w ≤ L * E ^ (1 / 2 : ℝ)) :
    fracNorm (auxCube m z) α r w < ⊤ :=
  hybrid_auxiliary_norm_finite hr hα m z hw (hbound.trans_lt (by finiteness))

end CoarseDeGiorgi.Assembly
