import CoarseDeGiorgi.Selection.Coarea
import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceSum
import CoarseDeGiorgi.Statements.SurfaceFracNorm

namespace CoarseDeGiorgi.Selection

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

variable {n : ℕ}

private def facePoint (i : Fin (n + 1)) (pos : Bool) (τ : ℝ) (u : Vec n) : Vec (n + 1) :=
  i.insertNth (if pos then τ / 2 else -τ / 2) u

private theorem measurable_facePoint (i : Fin (n + 1)) (pos : Bool) :
    Measurable (fun p : ℝ × Vec n => facePoint i pos p.1 p.2) := by
  have hp : Measurable (fun p : ℝ × Vec n => (if pos then p.1 / 2 else -p.1 / 2, p.2)) := by
    cases pos <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  exact (measurable_insertNth i).comp hp

private theorem measurable_variable_faceBox :
    MeasurableSet {p : ℝ × Vec n | p.2 ∈ faceBox n p.1} := by
  simp only [faceBox, mem_pi, mem_univ, forall_const, ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_lt (f := fun p : ℝ × Vec n => -p.1 / 2)
    (g := fun p => p.2 j) (by fun_prop) (by fun_prop)).inter
    (measurableSet_lt (f := fun p : ℝ × Vec n => p.2 j)
      (g := fun p => p.1 / 2) (by fun_prop) (by fun_prop))

/-- Both moving faces can be integrated with a jointly measurable parameter kernel. -/
theorem measurable_twoFaceIntegral (i j : Fin (n + 1)) (pos pos' : Bool)
    {K : Vec (n + 1) × Vec (n + 1) → ℝ≥0∞} (hK : Measurable K) :
    Measurable (fun τ => ∫⁻ xy, K xy
      ∂((CoarseDeGiorgi.cubeFaceMeasure τ i pos).prod (CoarseDeGiorgi.cubeFaceMeasure τ j pos'))) := by
  have : ∀ τ, IsFiniteMeasure (CoarseDeGiorgi.cubeFaceMeasure τ j pos') := fun τ => by
    change IsFiniteMeasure (Foundations.FracGeometry.faceMeasure τ j pos')
    infer_instance
  have he (τ : ℝ) :
      (∫⁻ xy, K xy ∂((CoarseDeGiorgi.cubeFaceMeasure τ i pos).prod (CoarseDeGiorgi.cubeFaceMeasure τ j pos'))) =
        ∫⁻ u in faceBox n τ, ∫⁻ v in faceBox n τ, K (facePoint i pos τ u, facePoint j pos' τ v) := by
    rw [lintegral_prod _ hK.aemeasurable]
    rw [lintegral_cubeFaceMeasure τ i pos hK.lintegral_prod_right']
    apply lintegral_congr
    intro u
    exact lintegral_cubeFaceMeasure τ j pos' (hK.comp measurable_prodMk_left)
  simp_rw [he, ← lintegral_indicator (measurableSet_faceBox n _)]
  have hinner : Measurable (fun z : ℝ × Vec n => ∫⁻ v : Vec n,
      (faceBox n z.1).indicator (fun v => K (facePoint i pos z.1 z.2, facePoint j pos' z.1 v)) v) := by
    apply Measurable.lintegral_prod_right (f := fun (z : ℝ × Vec n) (v : Vec n) =>
      (faceBox n z.1).indicator (fun v => K (facePoint i pos z.1 z.2, facePoint j pos' z.1 v)) v)
    change Measurable ({p : (ℝ × Vec n) × Vec n | p.2 ∈ faceBox n p.1.1}.indicator
      (fun p => K (facePoint i pos p.1.1 p.1.2, facePoint j pos' p.1.1 p.2)))
    apply Measurable.indicator
    · apply hK.comp
      exact ((measurable_facePoint i pos).comp measurable_fst).prodMk
        ((measurable_facePoint j pos').comp (measurable_fst.fst.prodMk measurable_snd))
    · exact measurable_variable_faceBox.preimage (measurable_fst.fst.prodMk measurable_snd)
  apply Measurable.lintegral_prod_right (f := fun τ u => (faceBox n τ).indicator
    (fun u => ∫⁻ v : Vec n, (faceBox n τ).indicator
      (fun v => K (facePoint i pos τ u, facePoint j pos' τ v)) v) u)
  change Measurable ({p : ℝ × Vec n | p.2 ∈ faceBox n p.1}.indicator _)
  exact hinner.indicator measurable_variable_faceBox

/-- The product surface measure includes all cross-face pairs; its integral is measurable in
the radius. -/
theorem measurable_surfaceProductIntegral
    {K : Vec (n + 1) × Vec (n + 1) → ℝ≥0∞} (hK : Measurable K) :
    Measurable (fun τ => ∫⁻ xy, K xy
      ∂((CoarseDeGiorgi.surfaceMeasure τ).prod (CoarseDeGiorgi.surfaceMeasure τ))) := by
  simp_rw [Foundations.FracGeometry.lintegral_surfaceMeasure_prod]
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun pos _ =>
    Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _ (fun pos' _ =>
      measurable_twoFaceIntegral i j pos pos' hK))))

/-- The surface fractional norm `surfaceFracNorm` is measurable in the radius. -/
theorem measurable_surfaceFracNorm {F : Vec (n + 1) → ℝ} (hF : Measurable F)
    (α : ℝ) {r : ℝ} (hr : 0 < r) :
    Measurable (fun τ => CoarseDeGiorgi.surfaceFracNorm τ α r F) := by
  have hpower : Measurable (fun τ => CoarseDeGiorgi.surfaceFracNorm τ α r F ^ r) := by
    simp_rw [Foundations.FracGeometry.surfaceNorm_power_eq _ α hr F hF]
    apply Measurable.add
    · exact measurable_surfaceIntegral (by fun_prop)
    · exact measurable_surfaceProductIntegral
        (Foundations.FracGeometry.measurable_euclidKernel _ _ hF)
  have he (τ : ℝ) : (CoarseDeGiorgi.surfaceFracNorm τ α r F ^ r) ^ (1 / r) =
      CoarseDeGiorgi.surfaceFracNorm τ α r F := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
  simpa only [he] using hpower.pow_const (1 / r)

/-- Surface fractional norms respect equality of representatives on that surface. -/
theorem surfaceFracNorm_congr_ae {d : ℕ} {τ α r : ℝ} {F G : Vec d → ℝ}
    (hFG : F =ᵐ[CoarseDeGiorgi.surfaceMeasure τ] G) :
    CoarseDeGiorgi.surfaceFracNorm τ α r F = CoarseDeGiorgi.surfaceFracNorm τ α r G := by
  have : IsFiniteMeasure (CoarseDeGiorgi.surfaceMeasure (d := d) τ) := by
    change IsFiniteMeasure (Foundations.FracGeometry.surfaceMeasure τ)
    infer_instance
  unfold CoarseDeGiorgi.surfaceFracNorm
  rw [eLpNorm_congr_ae hFG]
  congr 3
  unfold CoarseDeGiorgi.surfaceFracSeminorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hFG,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hFG] with xy hx hy
  change F xy.1 = G xy.1 at hx
  change F xy.2 = G xy.2 at hy
  simp only [CoarseDeGiorgi.fracKernelWithDimension, hx, hy]


end

end CoarseDeGiorgi.Selection
