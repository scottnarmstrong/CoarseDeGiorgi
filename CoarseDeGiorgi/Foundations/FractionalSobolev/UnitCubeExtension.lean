import CoarseDeGiorgi.Foundations.FractionalSobolev.UnitCubeReflection
import CoarseDeGiorgi.Statements.MemDnpvSobolev
import CoarseDeGiorgi.Statements.FracNorm
import CoarseDeGiorgi.Foundations.FracGeometry.Cutoff

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

lemma fracSeminorm_power {n : ℕ} (V : Set (Vec n)) (s : ℝ) {p : ℝ} (hp : 0 < p) (f : Vec n → ℝ) :
    fracSeminorm V s p f ^ p = ∫⁻ xy, fracKernel s p f xy ∂((volume.restrict V).prod (volume.restrict V)) := by
  unfold fracSeminorm
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

lemma fracNorm_power {n : ℕ} (V : Set (Vec n)) (s : ℝ) {p : ℝ} (hp : 0 < p) (f : Vec n → ℝ) :
    fracNorm V s p f ^ p = eLpNorm f (ENNReal.ofReal p) (volume.restrict V) ^ p + fracSeminorm V s p f ^ p := by
  unfold fracNorm
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

lemma lp_power_integral {n : ℕ} {μ : Measure (Vec n)} {f : Vec n → ℝ}
    (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, (ENNReal.ofReal |f x|) ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  simp only [Real.enorm_eq_ofReal_abs]

lemma fracSeminorm_congr_ae {n : ℕ} {V : Set (Vec n)} {f g : Vec n → ℝ}
    (hfg : f =ᵐ[volume.restrict V] g) (s p : ℝ) : fracSeminorm V s p f = fracSeminorm V s p g := by
  unfold fracSeminorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg, Measure.quasiMeasurePreserving_snd.ae_eq_comp hfg] with xy hx hy
  simp only [Function.comp_apply] at hx hy
  unfold fracKernel fracKernelWithDimension
  rw [hx, hy]

lemma fracNorm_congr_ae {n : ℕ} {V : Set (Vec n)} {f g : Vec n → ℝ}
    (hfg : f =ᵐ[volume.restrict V] g) (s p : ℝ) : fracNorm V s p f = fracNorm V s p g := by
  unfold fracNorm
  rw [eLpNorm_congr_ae hfg, fracSeminorm_congr_ae hfg s p]

lemma cubeFold_lp_power_le {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f) {p : ℝ} (hp : 0 < p) :
    eLpNorm (f ∘ cubeFold) (ENNReal.ofReal p) (volume.restrict (reflectedCube n)) ^ p ≤
      (3 ^ n : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) (volume.restrict (dnpvUnitCube n)) ^ p := by
  rw [lp_power_integral ((hf.comp cubeFold_continuous.measurable).aestronglyMeasurable.restrict) hp,
    lp_power_integral hf.aestronglyMeasurable.restrict hp]
  exact cubeFold_lintegral_le (fun x => (ENNReal.ofReal |f x|) ^ p)

lemma cubeFold_kernel_le {n : ℕ} {s p : ℝ} (hp : 0 < p) (hβ : 0 ≤ (n : ℝ) + s * p)
    (f : Vec n → ℝ) (x y : Vec n) :
    fracKernel s p (f ∘ cubeFold) (x, y) ≤ fracKernel s p f (cubeFold x, cubeFold y) := by
  by_cases hxy : cubeFold x = cubeFold y
  · simp only [fracKernel, fracKernelWithDimension, Function.comp_apply, hxy,
      sub_self, abs_zero, Real.zero_rpow hp.ne', zero_div, ENNReal.ofReal_zero, le_refl]
  · apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_pos_of_pos (euclidDist_pos hxy) _)
    exact Real.rpow_le_rpow (euclidDist_nonneg _ _) (cubeFold_distance_le x y) hβ

lemma cubeFold_seminorm_power_le {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f)
    {s p : ℝ} (hp : 0 < p) (hβ : 0 ≤ (n : ℝ) + s * p) :
    fracSeminorm (reflectedCube n) s p (f ∘ cubeFold) ^ p ≤
      (3 ^ n : ℝ≥0∞) * (3 ^ n : ℝ≥0∞) * fracSeminorm (dnpvUnitCube n) s p f ^ p := by
  rw [fracSeminorm_power _ _ hp, fracSeminorm_power _ _ hp,
    lintegral_prod _ (fracKernel_measurable (hf.comp cubeFold_continuous.measurable) s p).aemeasurable,
    lintegral_prod _ (fracKernel_measurable hf s p).aemeasurable]
  calc
    _ ≤ ∫⁻ x in reflectedCube n, ∫⁻ y in reflectedCube n, fracKernel s p f (cubeFold x, cubeFold y) :=
      lintegral_mono (fun x => lintegral_mono (cubeFold_kernel_le hp hβ f x))
    _ ≤ ∫⁻ x in reflectedCube n, (3 ^ n : ℝ≥0∞) * ∫⁻ y in dnpvUnitCube n, fracKernel s p f (cubeFold x, y) :=
      lintegral_mono (fun x => cubeFold_lintegral_le (fun y => fracKernel s p f (cubeFold x, y)))
    _ = (3 ^ n : ℝ≥0∞) * ∫⁻ x in reflectedCube n, ∫⁻ y in dnpvUnitCube n, fracKernel s p f (cubeFold x, y) :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ (3 ^ n : ℝ≥0∞) * ((3 ^ n : ℝ≥0∞) * ∫⁻ x in dnpvUnitCube n, ∫⁻ y in dnpvUnitCube n, fracKernel s p f (x, y)) :=
      mul_le_mul' le_rfl (cubeFold_lintegral_le (fun x => ∫⁻ y in dnpvUnitCube n, fracKernel s p f (x, y)))
    _ = _ := (mul_assoc _ _ _).symm

/-- A fixed Lipschitz multiplier, one on the closed unit cube and zero outside the unit ball. -/
def unitCubeCutoff {n : ℕ} (x : Vec n) : ℝ := max (min (2 - 2 * ‖x‖) 1) 0

lemma unitCubeCutoff_bound {n : ℕ} (x : Vec n) : |unitCubeCutoff x| ≤ 1 := by
  unfold unitCubeCutoff
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (min_le_right _ _) (by norm_num)

lemma unitCubeCutoff_eq_one {n : ℕ} {x : Vec n} (hx : x ∈ dnpvUnitCube n) : unitCubeCutoff x = 1 := by
  have hn : ‖x‖ ≤ (1 / 2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hx i).1], (hx i).2.le⟩
  unfold unitCubeCutoff
  rw [min_eq_right (by linarith), max_eq_left (by norm_num)]

lemma unitCubeCutoff_support {n : ℕ} {x : Vec n} (hx : unitCubeCutoff x ≠ 0) : ‖x‖ < 1 := by
  by_contra h
  apply hx
  unfold unitCubeCutoff
  rw [min_eq_left (by linarith [le_of_not_gt h]), max_eq_right (by linarith [le_of_not_gt h])]

lemma unitCubeCutoff_continuous {n : ℕ} : Continuous (unitCubeCutoff (n := n)) := by
  unfold unitCubeCutoff
  fun_prop

lemma unitCubeCutoff_lipschitz {n : ℕ} (x y : Vec n) :
    |unitCubeCutoff x - unitCubeCutoff y| ≤ euclidDist x y / (1 / 2) := by
  have hclamp : LipschitzWith 1 (fun t : ℝ => max (min t 1) 0) :=
    (LipschitzWith.id.min_const 1).max_const 0
  have h := hclamp.dist_le_mul (2 - 2 * ‖x‖) (2 - 2 * ‖y‖)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  have he : dist x y ≤ euclidDist x y := CoarseDeGiorgi.Foundations.Euclid.dist_le_eDist2 x y
  calc
    _ ≤ |2 - 2 * ‖x‖ - (2 - 2 * ‖y‖)| := h
    _ = 2 * |‖x‖ - ‖y‖| := by rw [show 2 - 2 * ‖x‖ - (2 - 2 * ‖y‖) = -2 * (‖x‖ - ‖y‖) by ring, abs_mul]; norm_num
    _ ≤ 2 * dist x y := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by norm_num)
    _ ≤ _ := by
      norm_num only [one_div, inv_inv, div_eq_mul_inv]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)

lemma unitCubeCutoff_separation {n : ℕ} {x : Vec n} (hx : unitCubeCutoff x ≠ 0)
    {y : Vec n} (hy : y ∉ reflectedCube n) : (1 / 2 : ℝ) ≤ euclidDist x y := by
  have hxnorm := unitCubeCutoff_support hx
  have hynorm : (3 / 2 : ℝ) ≤ ‖y‖ := by
    by_contra h
    apply hy
    intro i
    have hi := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at hi
    have hh : |y i| < 3 / 2 := hi.trans_lt (lt_of_not_ge h)
    exact ⟨by linarith [(abs_lt.mp hh).1], (abs_lt.mp hh).2⟩
  have he : dist x y ≤ euclidDist x y := CoarseDeGiorgi.Foundations.Euclid.dist_le_eDist2 x y
  have hn := norm_sub_norm_le y x
  rw [← dist_eq_norm, dist_comm] at hn
  linarith

/-- The reflected and cut off extension; zero outside the larger cube. -/
def unitCubeExtension {n : ℕ} (f : Vec n → ℝ) : Vec n → ℝ :=
  CoarseDeGiorgi.Foundations.FracGeometry.cutoffExtension (reflectedCube n) unitCubeCutoff (f ∘ cubeFold)

lemma unitCubeExtension_measurable {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f) : Measurable (unitCubeExtension f) :=
  CoarseDeGiorgi.Foundations.FracGeometry.measurable_cutoffExtension
    (reflectedCube_open n).measurableSet unitCubeCutoff_continuous.measurable (hf.comp cubeFold_continuous.measurable)

lemma unitCubeExtension_compact {n : ℕ} (f : Vec n → ℝ) : HasCompactSupport (unitCubeExtension f) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Vec n) 1)
  intro x hx
  have hφ : unitCubeCutoff x ≠ 0 := by
    intro hz
    apply hx
    simp [unitCubeExtension, CoarseDeGiorgi.Foundations.FracGeometry.cutoffExtension, hz]
  simpa only [Metric.mem_closedBall, dist_zero_right] using (unitCubeCutoff_support hφ).le

lemma unitCubeExtension_eq {n : ℕ} {f : Vec n → ℝ} {x : Vec n} (hx : x ∈ dnpvUnitCube n) : unitCubeExtension f x = f x := by
  have hV : x ∈ reflectedCube n := fun i => ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  rw [unitCubeExtension, CoarseDeGiorgi.Foundations.FracGeometry.cutoffExtension,
    Set.indicator_of_mem hV, unitCubeCutoff_eq_one hx, one_mul, Function.comp_apply, cubeFold_eq_self hx]

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
