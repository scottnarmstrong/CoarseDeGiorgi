import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceSum
import CoarseDeGiorgi.Foundations.FracGeometry.Defs
import CoarseDeGiorgi.Statements.FracNorm
import CoarseDeGiorgi.Statements.SurfaceFracNorm

namespace CoarseDeGiorgi.Foundations.FracGeometry
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

theorem slicing_representative_successor {n : ℕ} {F F' : Vec (n + 1) → ℝ}
    (hF : Measurable F) (hF' : Measurable F') (hEq : F =ᵐ[volume] F') :
    ∀ᵐ τ ∂(volume : Measure ℝ), F =ᵐ[surfaceMeasure τ] F' := by
  have hface (i : Fin (n + 1)) (pos : Bool) : ∀ᵐ τ ∂(volume : Measure ℝ), F =ᵐ[faceMeasure τ i pos] F' := by
    have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.quasiMeasurePreserving.ae_eq_comp hEq
    change ∀ᵐ p : ℝ × Vec n ∂(volume.prod volume), F (i.insertNth p.1 p.2) = F' (i.insertNth p.1 p.2) at hp
    have hl := Measure.ae_ae_of_ae_prod hp
    let a : ℝ := if pos then 1/2 else -(1/2)
    have ha : a ≠ 0 := by cases pos <;> norm_num [a]
    have hscaled := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) ha).ae hl
    have hparam : ∀ᵐ τ ∂(volume : Measure ℝ), ∀ᵐ u : Vec n ∂volume,
        F (i.insertNth (if pos then τ/2 else -τ/2) u) = F' (i.insertNth (if pos then τ/2 else -τ/2) u) := by
      have hc (τ : ℝ) : a • τ = if pos then τ/2 else -τ/2 := by cases pos <;> dsimp [a] <;> ring
      simpa only [hc] using hscaled
    filter_upwards [hparam] with τ hτ
    have hm : Measurable (fun u : Vec n => i.insertNth (α := fun _ => ℝ) (if pos then τ/2 else -τ/2) u) :=
      (isometry_insertNth i _).continuous.measurable
    have he : F =ᵐ[Measure.map (fun u : Vec n => i.insertNth (α := fun _ => ℝ) (if pos then τ/2 else -τ/2) u) volume] F' :=
      (ae_map_iff hm.aemeasurable (measurableSet_eq_fun hF hF')).mpr hτ
    exact he.filter_mono (faceMeasure_le_map_insertNth τ i pos).absolutelyContinuous.ae_le
  have hall := Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun pos => hface i pos
  filter_upwards [hall] with τ hτ
  rw [surfaceMeasure_eq_sum_faceMeasure]
  apply ae_finsetSum_measure_iff.mpr
  intro i _
  exact ae_finsetSum_measure_iff.mpr (fun pos _ => hτ i pos)

/-- The statement `fractional_slicing_ae_representative`, in all dimensions. -/
theorem fractional_slicing_ae_representative_proved {d : ℕ} {F F' : Vec d → ℝ}
    (hF : Measurable F) (hF' : Measurable F') (hEq : F =ᵐ[volume] F') :
    ∀ᵐ τ ∂(volume.restrict (Ioo (1/2 : ℝ) 1)), F =ᵐ[CoarseDeGiorgi.surfaceMeasure τ] F' := by
  cases d with
  | zero =>
    filter_upwards [] with τ
    change F =ᵐ[surfaceMeasure τ] F'
    rw [surfaceMeasure_zero_dim]
    simp only [Filter.EventuallyEq, ae_zero, Filter.eventually_bot]
  | succ n => exact (slicing_representative_successor hF hF' hEq).filter_mono Measure.restrict_le_self.absolutelyContinuous.ae_le
end
end CoarseDeGiorgi.Foundations.FracGeometry
