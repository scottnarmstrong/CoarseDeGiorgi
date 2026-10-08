import CoarseDeGiorgi.Foundations.FractionalSobolev.SurfaceEmbeddingCharts

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

instance embedding_surface_finite {d : ℕ} (τ : ℝ) : IsFiniteMeasure (surfaceMeasure (d := d) τ) := by
  change IsFiniteMeasure (FracGeometry.surfaceMeasure τ)
  infer_instance

lemma embedding_face_le_surface {d : ℕ} (τ : ℝ) (i : Fin d) (pos : Bool) :
    cubeFaceMeasure τ i pos ≤ surfaceMeasure τ := by
  classical
  apply Measure.le_iff.mpr
  intro A hA
  simp only [surfaceMeasure, Measure.finsetSum_apply]
  have hb : cubeFaceMeasure τ i pos A ≤ ∑ b : Bool, cubeFaceMeasure τ i b A :=
    Finset.single_le_sum (f := fun b : Bool => cubeFaceMeasure τ i b A)
      (fun _ _ => zero_le) (Finset.mem_univ pos)
  have hi : (∑ b : Bool, cubeFaceMeasure τ i b A) ≤
      ∑ j : Fin d, ∑ b : Bool, cubeFaceMeasure τ j b A :=
    Finset.single_le_sum (f := fun j : Fin d => ∑ b : Bool, cubeFaceMeasure τ j b A)
      (fun _ _ => zero_le) (Finset.mem_univ i)
  exact hb.trans hi

lemma embedding_surfaceNorm_power {d : ℕ} (τ α : ℝ) {r : ℝ} (hr : 0 < r) (g : Vec d → ℝ) :
    surfaceFracNorm τ α r g ^ r = eLpNorm g (ENNReal.ofReal r) (surfaceMeasure τ) ^ r +
      ∫⁻ xy, fracKernelWithDimension ((d : ℝ) - 1) α r g xy
        ∂((surfaceMeasure τ).prod (surfaceMeasure τ)) := by
  unfold surfaceFracNorm surfaceFracSeminorm
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one,
    ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

lemma embedding_surfaceKernel_measurable {d : ℕ} {g : Vec d → ℝ}
    (hg : Measurable g) (α r : ℝ) :
    Measurable (fracKernelWithDimension ((d : ℝ) - 1) α r g) := by
  unfold fracKernelWithDimension
  exact (((hg.comp measurable_fst).sub (hg.comp measurable_snd)).norm.pow_const _).div
    (euclidDist_continuous.measurable.pow_const _) |>.ennreal_ofReal

lemma embedding_chart_lp_le {n : ℕ} {τ : ℝ} (hτ : (1/2 : ℝ) ≤ τ) (hτ1 : τ ≤ 1)
    (i : Fin (n+1)) (pos : Bool) {g : Vec (n+1) → ℝ} (hg : Measurable g)
    {r : ℝ} (hr : 0 < r) :
    eLpNorm (g ∘ embeddingFaceChart τ i pos) (ENNReal.ofReal r)
        (volume.restrict (dnpvUnitCube n)) ^ r ≤
      (2 ^ n : ℝ≥0∞) * eLpNorm g (ENNReal.ofReal r) (surfaceMeasure τ) ^ r := by
  have hm := embeddingFaceChart_measurable τ i pos
  have hμ := (embeddingFaceChart_measure_bounds hτ hτ1 i pos).2.trans
    (smul_le_smul_left _ (embedding_face_le_surface τ i pos))
  rw [lp_power_integral (hg.comp hm).aestronglyMeasurable hr,
    lp_power_integral hg.aestronglyMeasurable hr]
  calc
    _ = ∫⁻ x, (ENNReal.ofReal |g x|) ^ r
        ∂Measure.map (embeddingFaceChart τ i pos) (volume.restrict (dnpvUnitCube n)) := by
      exact (lintegral_map (show Measurable (fun x => (ENNReal.ofReal |g x|) ^ r) from
        (hg.norm.ennreal_ofReal).pow_const r) hm).symm
    _ ≤ ∫⁻ x, (ENNReal.ofReal |g x|) ^ r ∂((2 ^ n : ℝ≥0∞) • surfaceMeasure τ) :=
      lintegral_mono' hμ le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

lemma embedding_chart_kernel_le {n : ℕ} {τ α r : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hr : 0 < r) (hβ : 0 ≤ (n : ℝ) + α * r) (i : Fin (n+1)) (pos : Bool)
    (g : Vec (n+1) → ℝ) (x y : Vec n) :
    fracKernel α r (g ∘ embeddingFaceChart τ i pos) (x,y) ≤
      fracKernelWithDimension ((n+1 : ℕ) - 1 : ℝ) α r g
        (embeddingFaceChart τ i pos x, embeddingFaceChart τ i pos y) := by
  by_cases hxy : x = y
  · simp only [fracKernel, fracKernelWithDimension, Function.comp_apply, hxy, sub_self,
      abs_zero, Real.zero_rpow hr.ne', zero_div, ENNReal.ofReal_zero, le_refl]
  · apply ENNReal.ofReal_le_ofReal
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Function.comp_apply]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_pos_of_pos (by rw [embeddingFaceChart_distance hτ.le]; exact mul_pos hτ (euclidDist_pos hxy)) _)
    apply Real.rpow_le_rpow (euclidDist_nonneg _ _) _ hβ
    rw [embeddingFaceChart_distance hτ.le]
    exact mul_le_of_le_one_left (euclidDist_nonneg x y) hτ1

lemma embedding_chart_energy_le {n : ℕ} {τ α r : ℝ}
    (hτ : (1/2 : ℝ) ≤ τ) (hτ1 : τ ≤ 1) (hr : 0 < r) (hβ : 0 ≤ (n : ℝ) + α * r)
    (i : Fin (n+1)) (pos : Bool) {g : Vec (n+1) → ℝ} (hg : Measurable g) :
    fracSeminorm (dnpvUnitCube n) α r (g ∘ embeddingFaceChart τ i pos) ^ r ≤
      ((2 ^ n : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)) *
        ∫⁻ xy, fracKernelWithDimension ((n+1 : ℕ) - 1 : ℝ) α r g xy
          ∂((surfaceMeasure τ).prod (surfaceMeasure τ)) := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have hm := embeddingFaceChart_measurable τ i pos
  let μ := volume.restrict (dnpvUnitCube n)
  let ψ := embeddingFaceChart τ i pos
  let K := fracKernelWithDimension ((n+1 : ℕ) - 1 : ℝ) α r g
  have hK : Measurable K := embedding_surfaceKernel_measurable hg α r
  have hμ : Measure.map ψ μ ≤ (2 ^ n : ℝ≥0∞) • surfaceMeasure τ :=
    (embeddingFaceChart_measure_bounds hτ hτ1 i pos).2.trans
      (smul_le_smul_left _ (embedding_face_le_surface τ i pos))
  rw [fracSeminorm_power _ _ hr]
  calc
    _ ≤ ∫⁻ xy, K (ψ xy.1, ψ xy.2) ∂(μ.prod μ) :=
      lintegral_mono (fun xy => embedding_chart_kernel_le hτ0 hτ1 hr hβ i pos g xy.1 xy.2)
    _ = ∫⁻ xy, K xy ∂((Measure.map ψ μ).prod (Measure.map ψ μ)) := by
      rw [Measure.map_prod_map μ μ (show Measurable ψ from hm) (show Measurable ψ from hm)]
      exact (lintegral_map hK (hm.prodMap hm)).symm
    _ ≤ ∫⁻ xy, K xy ∂(((2 ^ n : ℝ≥0∞) • surfaceMeasure τ).prod
        ((2 ^ n : ℝ≥0∞) • surfaceMeasure τ)) :=
      lintegral_mono' (Measure.prod_mono hμ hμ) le_rfl
    _ = _ := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, lintegral_smul_measure, smul_eq_mul]

/-- The normalized chart's full norm is controlled uniformly over every face. -/
lemma embedding_chart_norm_le {n : ℕ} {τ α r : ℝ}
    (hτ : (1/2 : ℝ) ≤ τ) (hτ1 : τ ≤ 1) (hr : 0 < r) (hβ : 0 ≤ (n : ℝ) + α * r)
    (i : Fin (n+1)) (pos : Bool) {g : Vec (n+1) → ℝ} (hg : Measurable g) :
    fracNorm (dnpvUnitCube n) α r (g ∘ embeddingFaceChart τ i pos) ≤
      ((2 ^ n : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)) ^ (1/r) * surfaceFracNorm τ α r g := by
  have ha : (1 : ℝ≥0∞) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hL := embedding_chart_lp_le hτ hτ1 i pos hg hr
  have hS := embedding_chart_energy_le hτ hτ1 hr hβ i pos hg
  apply (ENNReal.rpow_le_rpow_iff hr).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hr.ne', ENNReal.rpow_one, fracNorm_power _ _ hr,
    embedding_surfaceNorm_power _ _ hr, mul_add]
  exact add_le_add (hL.trans (mul_le_mul' (le_mul_of_one_le_right' ha) le_rfl)) hS

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
