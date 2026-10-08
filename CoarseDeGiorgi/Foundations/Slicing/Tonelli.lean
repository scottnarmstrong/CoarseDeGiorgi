module

public import CoarseDeGiorgi.Foundations.Slicing.MidpointAveraging

/-! The Tonelli step converting averaged surface kernels into exterior tails. -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Slicing

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The inverse-distance factor, with the real-power convention at zero. -/
def inversePower {d : ℕ} (q : ℝ) (x y : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (Euclid.eDist2 x y ^ (-q))

/-- One of the two symmetric midpoint-averaging contributions. -/
def averagedKernel {d : ℕ} (q r : ℝ) (F : Vec d → ℝ) (xy : Vec d × Vec d) : ℝ≥0∞ :=
  inversePower q xy.1 xy.2 *
    ∫⁻ z in euclidBall xy.1 (Euclid.eDist2 xy.1 xy.2), differencePower r F xy.1 z

/-- Rewriting the Euclidean fractional kernel as a product retains the diagonal. -/
theorem euclidKernel_eq_product {d : ℕ} (q r : ℝ) (F : Vec d → ℝ) (x y : Vec d) :
    Euclid.euclidKernel q r F (x, y) = differencePower r F x y * inversePower q x y := by
  dsimp only [Euclid.euclidKernel, differencePower, inversePower]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
    Real.rpow_neg (Euclid.eDist2_nonneg _ _), div_eq_mul_inv]

theorem measurable_inversePower {d : ℕ} (q : ℝ) :
    Measurable (fun xy : Vec d × Vec d => inversePower q xy.1 xy.2) :=
  (Euclid.continuous_eDist2.measurable.pow measurable_const).ennreal_ofReal

private theorem measurable_averagingIntegrand {d : ℕ} (q r : ℝ)
    {F : Vec d → ℝ} (hF : Measurable F) :
    Measurable (fun p : (Vec d × Vec d) × Vec d =>
      if Euclid.eDist2 p.1.1 p.2 < Euclid.eDist2 p.1.1 p.1.2 then
        inversePower q p.1.1 p.1.2 * differencePower r F p.1.1 p.2 else 0) := by
  have hx : Measurable (fun p : (Vec d × Vec d) × Vec d => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hy : Measurable (fun p : (Vec d × Vec d) × Vec d => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hz : Measurable (fun p : (Vec d × Vec d) × Vec d => p.2) := measurable_snd
  have hdxz := Euclid.continuous_eDist2.measurable.comp (hx.prodMk hz)
  have hdxy := Euclid.continuous_eDist2.measurable.comp (hx.prodMk hy)
  have hdiff : Measurable (fun p : (Vec d × Vec d) × Vec d =>
      differencePower r F p.1.1 p.2) := by
    change Measurable (fun p : (Vec d × Vec d) × Vec d => ENNReal.ofReal (|F p.1.1 - F p.2| ^ r))
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Function.comp_def] using
      (((hF.comp hx).sub (hF.comp hz)).norm.pow measurable_const).ennreal_ofReal
  exact Measurable.piecewise (measurableSet_lt hdxz hdxy)
    (((measurable_inversePower q).comp measurable_fst).mul hdiff) measurable_const

theorem averagedKernel_eq_lintegral {d : ℕ} (q r : ℝ) (F : Vec d → ℝ)
    (xy : Vec d × Vec d) :
    averagedKernel q r F xy = ∫⁻ z,
      if Euclid.eDist2 xy.1 z < Euclid.eDist2 xy.1 xy.2 then
        inversePower q xy.1 xy.2 * differencePower r F xy.1 z else 0 := by
  rw [averagedKernel, ← lintegral_const_mul' _ _
    (show inversePower q xy.1 xy.2 ≠ ⊤ from ENNReal.ofReal_ne_top),
    ← lintegral_indicator (measurableSet_euclidBall _ _)]
  apply lintegral_congr
  intro z
  rfl

theorem measurable_averagedKernel {d : ℕ} (q r : ℝ) {F : Vec d → ℝ}
    (hF : Measurable F) : Measurable (averagedKernel q r F) := by
  simp_rw [funext (averagedKernel_eq_lintegral q r F)]
  exact (measurable_averagingIntegrand q r hF).lintegral_prod_right'

/-- Tonelli exchanges the ball average and the surface variable. -/
theorem lintegral_averagedKernel_row {d : ℕ} (μ : Measure (Vec d)) [SFinite μ]
    (q r : ℝ) {F : Vec d → ℝ} (hF : Measurable F) (x : Vec d) :
    (∫⁻ y, averagedKernel q r F (x, y) ∂μ) =
      ∫⁻ z, differencePower r F x z *
        ∫⁻ y in {y | Euclid.eDist2 x z < Euclid.eDist2 x y}, inversePower q x y ∂μ := by
  simp_rw [averagedKernel_eq_lintegral]
  have hmeas : Measurable (fun p : Vec d × Vec d =>
      if Euclid.eDist2 x p.2 < Euclid.eDist2 x p.1 then
        inversePower q x p.1 * differencePower r F x p.2 else 0) :=
    (measurable_averagingIntegrand q r hF).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  apply lintegral_congr
  intro z
  have hset : MeasurableSet {y : Vec d | Euclid.eDist2 x z < Euclid.eDist2 x y} := by
    apply measurableSet_lt measurable_const
    exact Euclid.continuous_eDist2.measurable.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_const_mul' _ _
    (show differencePower r F x z ≠ ⊤ from ENNReal.ofReal_ne_top),
    ← lintegral_indicator hset]
  apply lintegral_congr
  intro y
  by_cases h : Euclid.eDist2 x z < Euclid.eDist2 x y
  · simp only [h, ite_true, indicator_of_mem (show y ∈ {y | Euclid.eDist2 x z < Euclid.eDist2 x y} from h), mul_comm]
  · simp only [h, ite_false, indicator_of_notMem (show y ∉ {y | Euclid.eDist2 x z < Euclid.eDist2 x y} from h)]

/-- The pointwise fractional kernel is controlled by the two midpoint terms. -/
theorem euclidKernel_le_averaged {d : ℕ} {r : ℝ} (hr : 0 < r)
    {F : Vec d → ℝ} (hF : Measurable F) (β : ℝ) (x y : Vec d) :
    Euclid.euclidKernel β r F (x, y) ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ d) * (2 : ℝ≥0∞) ^ r *
        (averagedKernel (β + d) r F (x, y) + averagedKernel (β + d) r F (y, x)) := by
  by_cases hxy : x = y
  · subst y
    simp only [Euclid.euclidKernel, sub_self, abs_zero, Real.zero_rpow hr.ne',
      zero_div, ENNReal.ofReal_zero]
    exact bot_le
  have hsym : Euclid.eDist2 y x = Euclid.eDist2 x y := by
    simp only [Euclid.eDist2, Euclid.eNorm2_eq_norm_toLp, WithLp.toLp_sub, norm_sub_rev]
  have hℓ := Euclid.eDist2_pos hxy
  rw [euclidKernel_eq_product]
  have h := mul_le_mul_left (differencePower_le_midpoint_average hr hF hxy)
    (inversePower β x y)
  refine h.trans_eq ?_
  dsimp only [averagedKernel, inversePower, Prod.fst, Prod.snd]
  rw [hsym]
  have hc : ENNReal.ofReal (Euclid.eDist2 x y ^ (-(d : ℝ))) *
      ENNReal.ofReal (Euclid.eDist2 x y ^ (-β)) =
      ENNReal.ofReal (Euclid.eDist2 x y ^ (-(β + d))) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le _),
      ← Real.rpow_add hℓ, show -(d : ℝ) + -β = -(β + d) by ring]
  calc
    _ = ENNReal.ofReal (((d : ℝ) + 1) ^ d) * (2 : ℝ≥0∞) ^ r *
        (ENNReal.ofReal (Euclid.eDist2 x y ^ (-(d : ℝ))) *
          ENNReal.ofReal (Euclid.eDist2 x y ^ (-β))) *
        ((∫⁻ z in euclidBall x (Euclid.eDist2 x y), differencePower r F x z) +
          ∫⁻ z in euclidBall y (Euclid.eDist2 x y), differencePower r F y z) := by ring
    _ = _ := by rw [hc]; ring

end

end CoarseDeGiorgi.Foundations.Slicing
