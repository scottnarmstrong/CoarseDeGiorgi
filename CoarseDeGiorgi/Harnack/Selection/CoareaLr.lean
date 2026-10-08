module

public import CoarseDeGiorgi.Selection.TraceBounds
public import CoarseDeGiorgi.Selection.CoareaPartition
public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Selection

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The Lr surface trace has the source coarea integral bound on the selected radius interval,
and therefore on the full annulus and the containing cube. -/
theorem surface_Lr_integral_le {n : ℕ} {ρ R r : ℝ} (hρ : 0 ≤ ρ) (hgap : ρ < R)
    (hr : 0 < r) {v : Vec (n + 1) → ℝ} (hv : Measurable v) :
    (∫⁻ τ in CoarseDeGiorgi.Selection.selectionInterval ρ R,
      eLpNorm v (ENNReal.ofReal r) (CoarseDeGiorgi.surfaceMeasure τ) ^ r) ≤
      2 * eLpNorm v (ENNReal.ofReal r)
        (volume.restrict (CoarseDeGiorgi.originCube R)) ^ r := by
  let g : Vec (n + 1) → ℝ≥0∞ := fun x => ENNReal.ofReal (|v x| ^ r)
  have hg : Measurable g := by fun_prop
  have he (μ : Measure (Vec (n + 1))) :
      eLpNorm v (ENNReal.ofReal r) μ ^ r = ∫⁻ x, g x ∂μ := by
    rw [Foundations.FracGeometry.eLpNorm_ofReal_rpow hr hv]
  have hAnn : CoarseDeGiorgi.Selection.cubicalAnnulus (n + 1) ρ R ⊆
      CoarseDeGiorgi.originCube R := by
    intro x hx i
    change ρ / 2 < ‖x‖ ∧ ‖x‖ < R / 2 at hx
    have hi : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact abs_lt.mp (by linarith only [hi, hx.2])
  have hleft :
      (∫⁻ τ in CoarseDeGiorgi.Selection.selectionInterval ρ R,
        eLpNorm v (ENNReal.ofReal r) (CoarseDeGiorgi.surfaceMeasure τ) ^ r) =
      ∫⁻ τ in CoarseDeGiorgi.Selection.selectionInterval ρ R,
        ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ := by
    apply lintegral_congr
    intro τ
    exact he (CoarseDeGiorgi.surfaceMeasure τ)
  have hright :
      eLpNorm v (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.originCube R)) ^ r =
        ∫⁻ x in CoarseDeGiorgi.originCube R, g x :=
    he (volume.restrict (CoarseDeGiorgi.originCube R))
  rw [hleft, hright]
  calc
    (∫⁻ τ in CoarseDeGiorgi.Selection.selectionInterval ρ R,
        ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ) ≤
      ∫⁻ τ in Ioo ρ R, ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ :=
        lintegral_mono_set (CoarseDeGiorgi.Selection.selectionInterval_subset hgap)
    _ = 2 * ∫⁻ x in CoarseDeGiorgi.Selection.cubicalAnnulus (n + 1) ρ R, g x :=
      CoarseDeGiorgi.Selection.cubical_coarea hρ hg
    _ ≤ 2 * ∫⁻ x in CoarseDeGiorgi.originCube R, g x := by
      gcongr
    _ = 2 * ∫⁻ x, g x ∂volume.restrict (CoarseDeGiorgi.originCube R) := rfl

end
end CoarseDeGiorgi.Harnack.Selection
