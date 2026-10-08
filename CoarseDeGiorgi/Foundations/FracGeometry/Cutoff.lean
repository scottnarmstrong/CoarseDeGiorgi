import CoarseDeGiorgi.Foundations.FracGeometry.CutoffPointwise
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The nonnegative radial multiplier kernel, with the zero-at-origin convention. -/
def cutoffRadial (α r ε : ℝ) (z : Vec d) : ℝ :=
  (min 2 (Euclid.eNorm2 z / ε)) ^ r / Euclid.eNorm2 z ^ ((d : ℝ) + α * r)

theorem cutoffRadial_nonneg (α r : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (z : Vec d) :
    0 ≤ cutoffRadial α r ε z :=
  div_nonneg (Real.rpow_nonneg (le_min (by norm_num)
    (div_nonneg (Euclid.eNorm2_nonneg z) hε)) _)
    (Real.rpow_nonneg (Euclid.eNorm2_nonneg z) _)

theorem measurable_cutoffRadial (α r ε : ℝ) : Measurable (cutoffRadial (d := d) α r ε) := by
  unfold cutoffRadial
  exact ((measurable_const.min (Euclid.continuous_eNorm2.measurable.div_const ε)).pow
    measurable_const).div (Euclid.continuous_eNorm2.measurable.pow measurable_const)

variable [NeZero d]

/-- The unit-radius multiplier is integrable: the two radial exponents are
`r(1-α)-1` at zero and `-αr-1` at infinity. -/
theorem integrable_cutoffRadial_one {α r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 0 < r) : Integrable (cutoffRadial (d := d) α r 1) := by
  let β : ℝ := (d : ℝ) + α * r
  let C : ℝ := Real.sqrt (d : ℝ) ^ r
  let g : ℝ → ℝ := fun t => if t ≤ 1 then C * t ^ (r - β) else 2 ^ r * t ^ (-β)
  have hd : 0 < d := NeZero.pos d
  have hdR : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have hdim : Module.finrank ℝ (Vec d) = d := Module.finrank_fin_fun ℝ
  have hnear : IntegrableOn (fun t : ℝ => t ^ (r - α * r - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by nlinarith only [hr, hα1])).1
  have hfar : IntegrableOn (fun t : ℝ => t ^ (-α * r - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by nlinarith only [hr, hα0]) zero_lt_one
  have hweight (t : ℝ) (ht : 0 < t) (q : ℝ) :
      t ^ (d - 1) * t ^ q = t ^ ((d : ℝ) - 1 + q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht, hdR]
  have hg : Integrable (fun z : Vec d => g ‖z‖) := by
    rw [integrable_fun_norm_addHaar volume, hdim]
    have hn : IntegrableOn (fun t : ℝ => t ^ (d - 1) • g t) (Ioc 0 1) := by
      apply IntegrableOn.congr_fun (hnear.const_mul C) _ measurableSet_Ioc
      intro t ht
      simp only [g, ite_eq_left ht.2, smul_eq_mul]
      rw [mul_left_comm, hweight t ht.1]
      congr 2
      dsimp only [β]
      ring
    have hf : IntegrableOn (fun t : ℝ => t ^ (d - 1) • g t) (Ioi 1) := by
      apply IntegrableOn.congr_fun (hfar.const_mul (2 ^ r)) _ measurableSet_Ioi
      intro t ht
      have ht' : 1 < t := ht
      simp only [g, ite_eq_right (not_le.mpr ht'), smul_eq_mul]
      rw [mul_left_comm, hweight t (zero_lt_one.trans ht')]
      congr 2
      dsimp only [β]
      ring
    have hu : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
      ext t
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · rintro (⟨h0, _⟩ | h1)
        · exact h0
        · exact zero_lt_one.trans h1
      · intro h0
        by_cases h1 : t ≤ 1
        · exact Or.inl ⟨h0, h1⟩
        · exact Or.inr (not_le.mp h1)
    rw [← hu]
    exact hn.union hf
  refine hg.mono' (measurable_cutoffRadial α r 1).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro z
  have he := Euclid.eNorm2_nonneg z
  have hC : 0 ≤ C := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hβ : 0 < β := by dsimp only [β]; positivity
  by_cases hz : z = 0
  · subst z
    simp only [cutoffRadial, Euclid.eNorm2_zero, zero_div, min_eq_right (by norm_num : (0:ℝ) ≤ 2),
      Real.zero_rpow hr.ne', zero_div, norm_zero, g, ite_eq_left zero_le_one]
    positivity
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hden : Euclid.eNorm2 z ^ (-β) ≤ ‖z‖ ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hn (Euclid.norm_le_eNorm2 z) (neg_nonpos.mpr hβ.le)
  have hm : 0 ≤ min 2 (Euclid.eNorm2 z) := le_min (by norm_num) he
  change |cutoffRadial α r 1 z| ≤ g ‖z‖
  rw [abs_of_nonneg (cutoffRadial_nonneg α r zero_le_one z)]
  unfold cutoffRadial
  rw [div_one, div_eq_mul_inv, ← Real.rpow_neg he]
  by_cases hzn : ‖z‖ ≤ 1
  · have hnum : (min 2 (Euclid.eNorm2 z)) ^ r ≤ C * ‖z‖ ^ r := by
      calc
        _ ≤ Euclid.eNorm2 z ^ r := Real.rpow_le_rpow hm (min_le_right _ _) hr.le
        _ ≤ (Real.sqrt (d : ℝ) * ‖z‖) ^ r :=
          Real.rpow_le_rpow he (Euclid.eNorm2_le_sqrt_mul_norm z) hr.le
        _ = _ := Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)
    simp only [g, ite_eq_left hzn]
    calc
      _ ≤ (C * ‖z‖ ^ r) * ‖z‖ ^ (-β) :=
        mul_le_mul hnum hden (Real.rpow_nonneg he _) (mul_nonneg hC (Real.rpow_nonneg hn.le _))
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hn]; rfl
  · simp only [g, ite_eq_right hzn]
    exact mul_le_mul (Real.rpow_le_rpow hm (min_le_left _ _) hr.le) hden
      (Real.rpow_nonneg he _) (Real.rpow_nonneg (by norm_num) _)

omit [NeZero d] in
/-- Dilation of the multiplier kernel, before integration. -/
theorem cutoffRadial_smul (α r : ℝ) {ε : ℝ} (hε : 0 < ε) (z : Vec d) :
    cutoffRadial α r ε (ε • z) =
      ε ^ (-((d : ℝ) + α * r)) * cutoffRadial α r 1 z := by
  simp only [cutoffRadial, Euclid.eNorm2_smul, abs_of_pos hε, div_one,
    mul_div_cancel_left₀ _ hε.ne']
  rw [Real.mul_rpow hε.le (Euclid.eNorm2_nonneg z), Real.rpow_neg hε.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integrable_cutoffRadial {α r ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 0 < r) (hε : 0 < ε) : Integrable (cutoffRadial (d := d) α r ε) := by
  have h := (integrable_cutoffRadial_one (d := d) hα0 hα1 hr).const_mul
    (ε ^ (-((d : ℝ) + α * r)))
  apply (integrable_comp_smul_iff volume (cutoffRadial α r ε) hε.ne').1
  exact h.congr (Filter.Eventually.of_forall fun z => (cutoffRadial_smul α r hε z).symm)

omit [NeZero d] in
/-- Exact scaling of the finite Euclidean radial integral. -/
theorem integral_cutoffRadial {α r ε : ℝ} (hε : 0 < ε) :
    (∫ z : Vec d, cutoffRadial α r ε z) =
      ε ^ (-α * r) * ∫ z : Vec d, cutoffRadial α r 1 z := by
  have hpoint (z : Vec d) : cutoffRadial α r ε z =
      ε ^ (-((d : ℝ) + α * r)) * cutoffRadial α r 1 (ε⁻¹ • z) := by
    have hz := cutoffRadial_smul α r hε (ε⁻¹ • z)
    rwa [smul_smul, mul_inv_cancel₀ hε.ne', one_smul] at hz
  simp_rw [hpoint]
  rw [integral_const_mul, Measure.integral_comp_inv_smul,
    Module.finrank_fin_fun, abs_of_pos (pow_pos hε _), smul_eq_mul,
    ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hε]
  congr 2
  ring

/-- The radial integral has a finite constant depending only on d, α, r. -/
theorem lintegral_cutoffRadial {α r ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 0 < r) (hε : 0 < ε) :
    (∫⁻ z : Vec d, ENNReal.ofReal (cutoffRadial α r ε z)) =
      ENNReal.ofReal (ε ^ (-α * r)) *
        ENNReal.ofReal (∫ z : Vec d, cutoffRadial α r 1 z) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_cutoffRadial hα0 hα1 hr hε)
    (Filter.Eventually.of_forall (cutoffRadial_nonneg α r hε.le)),
    integral_cutoffRadial hε, ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]

end
end CoarseDeGiorgi.Foundations.FracGeometry

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section
variable {d : ℕ}

/-- Domain-restricted r-th power of the function. -/
def cutoffMass (V : Set (Vec d)) (r : ℝ) (w : Vec d → ℝ) : Vec d → ℝ≥0∞ :=
  V.indicator (fun x => ENNReal.ofReal (|w x| ^ r))

/-- Interior pairs, viewed as a whole-space integrand. -/
def cutoffInterior (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) :
    Vec d × Vec d → ℝ≥0∞ :=
  (V ×ˢ V).indicator (Euclid.euclidKernel ((d : ℝ) + α * r) r w)

/-- The multiplier error attached to the second endpoint. -/
def cutoffError (V : Set (Vec d)) (α r ε : ℝ) (w : Vec d → ℝ)
    (xy : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (cutoffRadial α r ε (xy.1 - xy.2)) * cutoffMass V r w xy.2

theorem cutoffRadial_sub_swap (α r ε : ℝ) (x y : Vec d) :
    cutoffRadial α r ε (y - x) = cutoffRadial α r ε (x - y) := by
  have hn : Euclid.eNorm2 (y - x) = Euclid.eNorm2 (x - y) := by
    rw [← neg_sub x y, show -(x - y) = (-1 : ℝ) • (x - y) by simp,
      Euclid.eNorm2_smul]
    norm_num
  simp only [cutoffRadial, hn]

/-- The raw kernel factorization also holds on the diagonal. -/
theorem cutoff_kernel_factor (β r : ℝ) (w : Vec d → ℝ) (xy : Vec d × Vec d) :
    Euclid.euclidKernel β r w xy = ENNReal.ofReal (|w xy.1 - w xy.2| ^ r) *
      ENNReal.ofReal (euclidDist xy.1 xy.2 ^ (-β)) := by
  unfold Euclid.euclidKernel
  rw [euclidDist_eq_eDist2, Real.rpow_neg (Euclid.eDist2_nonneg _ _), div_eq_mul_inv,
    ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]

theorem cutoff_radial_factor (α r ε : ℝ) (hε : 0 < ε) (x y : Vec d) :
    ENNReal.ofReal (cutoffRadial α r ε (x - y)) =
      ENNReal.ofReal ((min 2 (euclidDist x y / ε)) ^ r) *
        ENNReal.ofReal (euclidDist x y ^ (-((d : ℝ) + α * r))) := by
  have hm : 0 ≤ min 2 (euclidDist x y / ε) := le_min (by norm_num)
    (div_nonneg (Euclid.eDist2_nonneg x y) hε.le)
  change ENNReal.ofReal ((min 2 (euclidDist x y / ε)) ^ r /
    euclidDist x y ^ ((d : ℝ) + α * r)) = _
  rw [euclidDist_eq_eDist2] at hm
  rw [euclidDist_eq_eDist2, Real.rpow_neg (Euclid.eDist2_nonneg _ _), div_eq_mul_inv,
    ENNReal.ofReal_mul (Real.rpow_nonneg hm _)]

theorem measurable_cutoffInterior {V : Set (Vec d)} (hV : MeasurableSet V)
    (α r : ℝ) {w : Vec d → ℝ} (hw : Measurable w) :
    Measurable (cutoffInterior V α r w) := by
  unfold cutoffInterior Euclid.euclidKernel
  exact (((hw.comp measurable_fst).sub (hw.comp measurable_snd)).norm.pow
    measurable_const |>.div (Euclid.continuous_eDist2.measurable.pow measurable_const)
    |>.ennreal_ofReal).indicator (hV.prod hV)

theorem measurable_cutoffError {V : Set (Vec d)} (hV : MeasurableSet V)
    (α r ε : ℝ) {w : Vec d → ℝ} (hw : Measurable w) :
    Measurable (cutoffError V α r ε w) := by
  unfold cutoffError cutoffMass
  exact ((measurable_cutoffRadial α r ε).comp (measurable_fst.sub measurable_snd)
    |>.ennreal_ofReal).mul
    (((hw.norm.pow measurable_const).ennreal_ofReal.indicator hV).comp measurable_snd)

/-- Separation controls mixed pairs by the same multiplier kernel as interior pairs. -/
theorem cutoff_mixed_difference {V : Set (Vec d)} {ε : ℝ} (hε : 0 < ε)
    {φ : Vec d → ℝ} (hBound : ∀ x, |φ x| ≤ 1)
    (hSep : ∀ x ∈ Function.support φ, ∀ y ∉ V, ε ≤ euclidDist x y)
    (w : Vec d → ℝ) (x y : Vec d) (hy : y ∉ V) :
    |φ x * w x| ≤ min 2 (euclidDist x y / ε) * |w x| := by
  have hm : 0 ≤ min 2 (euclidDist x y / ε) := le_min (by norm_num)
    (div_nonneg (Euclid.eDist2_nonneg x y) hε.le)
  by_cases hφ : φ x = 0
  · rw [hφ, zero_mul, abs_zero]
    exact mul_nonneg hm (abs_nonneg _)
  · have hm1 : 1 ≤ min 2 (euclidDist x y / ε) :=
      le_min (by norm_num) ((le_div_iff₀ hε).2 (by simpa only [one_mul] using hSep x hφ y hy))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((hBound x).trans hm1) (abs_nonneg _)

/-- Mixed pairs are dominated without assuming a radial-tail estimate. -/
theorem cutoff_mixed_kernel {V : Set (Vec d)} {α r ε : ℝ}
    (hε : 0 < ε) (hr : 0 < r) {φ : Vec d → ℝ} (hBound : ∀ x, |φ x| ≤ 1)
    (hSep : ∀ x ∈ Function.support φ, ∀ y ∉ V, ε ≤ euclidDist x y)
    (w : Vec d → ℝ) (xy : Vec d × Vec d) (hx : xy.1 ∈ V) (hy : xy.2 ∉ V) :
    Euclid.euclidKernel ((d : ℝ) + α * r) r (cutoffExtension V φ w) xy ≤
      cutoffError V α r ε w xy.swap := by
  have hm : 0 ≤ min 2 (euclidDist xy.1 xy.2 / ε) := le_min (by norm_num)
    (div_nonneg (Euclid.eDist2_nonneg _ _) hε.le)
  have hn := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _)
    (cutoff_mixed_difference hε hBound hSep w xy.1 xy.2 hy) hr.le)
  rw [Real.mul_rpow hm (abs_nonneg _), ENNReal.ofReal_mul (Real.rpow_nonneg hm _)] at hn
  rw [cutoff_kernel_factor]
  simp only [cutoffExtension, indicator_of_mem hx, indicator_of_notMem hy, sub_zero]
  have h := mul_le_mul_right hn (ENNReal.ofReal
    (euclidDist xy.1 xy.2 ^ (-((d : ℝ) + α * r))))
  simpa only [cutoffError, Prod.fst_swap, Prod.snd_swap, cutoffRadial_sub_swap,
    cutoffMass, indicator_of_mem hx, cutoff_radial_factor α r ε hε,
    mul_assoc, mul_comm, mul_left_comm] using h

/-- Pointwise domination covering all four interior/exterior configurations. -/
theorem cutoff_kernel_le {V : Set (Vec d)} {α r ε : ℝ}
    (hε : 0 < ε) (hr : 0 < r) {φ : Vec d → ℝ}
    (hBound : ∀ x, |φ x| ≤ 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ euclidDist x y / ε)
    (hSep : ∀ x ∈ Function.support φ, ∀ y ∉ V, ε ≤ euclidDist x y)
    (w : Vec d → ℝ) (xy : Vec d × Vec d) :
    Euclid.euclidKernel ((d : ℝ) + α * r) r (cutoffExtension V φ w) xy ≤
      (2 : ℝ≥0∞) ^ r * (cutoffInterior V α r w xy +
        cutoffError V α r ε w xy + cutoffError V α r ε w xy.swap) := by
  have h2 : (1 : ℝ≥0∞) ≤ 2 ^ r := ENNReal.one_le_rpow (by norm_num) hr
  by_cases hx : xy.1 ∈ V <;> by_cases hy : xy.2 ∈ V
  · have hp := mul_le_mul_right
      (cutoff_product_rpow_le hε hr hBound hLip w xy.1 xy.2)
      (ENNReal.ofReal (euclidDist xy.1 xy.2 ^ (-((d : ℝ) + α * r))))
    have hin : xy ∈ V ×ˢ V := ⟨hx, hy⟩
    have hb : Euclid.euclidKernel ((d : ℝ) + α * r) r (cutoffExtension V φ w) xy ≤
        2 ^ r * (cutoffInterior V α r w xy + cutoffError V α r ε w xy) := by
      simpa only [cutoff_kernel_factor, cutoffExtension, indicator_of_mem hx,
        indicator_of_mem hy, cutoffInterior, indicator_of_mem hin,
        cutoffError, cutoffMass, cutoff_radial_factor α r ε hε,
        mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hp
    exact hb.trans (mul_le_mul_right (le_add_right le_rfl) _)
  · exact (cutoff_mixed_kernel hε hr hBound hSep w xy hx hy).trans
      ((le_add_left le_rfl).trans
        (le_mul_of_one_le_left' h2))
  · have h := cutoff_mixed_kernel (α := α) hε hr hBound hSep w xy.swap hy hx
    have heq : Euclid.euclidKernel ((d : ℝ) + α * r) r (cutoffExtension V φ w) xy.swap =
        Euclid.euclidKernel ((d : ℝ) + α * r) r (cutoffExtension V φ w) xy := by
      simp only [Euclid.euclidKernel, Prod.fst_swap, Prod.snd_swap, abs_sub_comm]
      rw [show Euclid.eDist2 xy.2 xy.1 = Euclid.eDist2 xy.1 xy.2 by
        unfold Euclid.eDist2; rw [← neg_sub xy.1 xy.2];
        simp only [Euclid.eNorm2_eq_norm_toLp, WithLp.toLp_neg, norm_neg]]
    rw [heq, Prod.swap_swap] at h
    exact h.trans ((le_add_right (le_add_left le_rfl)).trans (le_mul_of_one_le_left' h2))
  · simp only [Euclid.euclidKernel, cutoffExtension, indicator_of_notMem hx,
      indicator_of_notMem hy, sub_self, abs_zero, Real.zero_rpow hr.ne', zero_div,
      ENNReal.ofReal_zero, zero_le]


/-- Exact unnormalized raw integral underlying the copied seminorm. -/
theorem fracSeminorm_rpow (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Vec d → ℝ) : fracSeminorm V α r w ^ r =
      ∫⁻ xy, Euclid.euclidKernel ((d : ℝ) + α * r) r w xy
        ∂((volume.restrict V).prod (volume.restrict V)) := by
  rw [fracSeminorm_eq_eFracSeminorm, Euclid.eFracSeminorm,
    ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

theorem lintegral_cutoffInterior {V : Set (Vec d)} (hV : MeasurableSet V)
    (α : ℝ) {r : ℝ} (hr : 0 < r) (w : Vec d → ℝ) :
    (∫⁻ xy, cutoffInterior V α r w xy ∂volume.prod volume) = fracSeminorm V α r w ^ r := by
  rw [fracSeminorm_rpow V α hr w, cutoffInterior,
    lintegral_indicator (hV.prod hV), ← Measure.prod_restrict]

theorem lintegral_cutoffMass {V : Set (Vec d)} (hV : MeasurableSet V)
    {r : ℝ} (hr : 0 < r) {w : Vec d → ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict V)) :
    (∫⁻ x, cutoffMass V r w x) = eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ^ r := by
  rw [cutoffMass, lintegral_indicator hV,
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top hw,
    ENNReal.toReal_ofReal hr.le, ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hr]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr.le]

variable [NeZero d]

/-- Tonelli and translation give the complete multiplier-error integral. -/
theorem lintegral_cutoffError {V : Set (Vec d)} (hV : MeasurableSet V)
    {α r ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hε : 0 < ε)
    {w : Vec d → ℝ} (hw : Measurable w) :
    (∫⁻ xy, cutoffError V α r ε w xy ∂volume.prod volume) =
      ENNReal.ofReal (ε ^ (-α * r)) *
        ENNReal.ofReal (∫ z : Vec d, cutoffRadial α r 1 z) *
          eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ^ r := by
  rw [lintegral_prod_symm' _ (measurable_cutoffError hV α r ε hw)]
  have hinner (y : Vec d) :
      (∫⁻ x, cutoffError V α r ε w (x, y)) =
        (ENNReal.ofReal (ε ^ (-α * r)) *
          ENNReal.ofReal (∫ z : Vec d, cutoffRadial α r 1 z)) * cutoffMass V r w y := by
    change (∫⁻ x, ENNReal.ofReal (cutoffRadial α r ε (x - y)) * cutoffMass V r w y) = _
    rw [lintegral_mul_const _ (show Measurable (fun x : Vec d =>
      ENNReal.ofReal (cutoffRadial α r ε (x - y))) from
        ((measurable_cutoffRadial α r ε).comp (measurable_id.sub_const y)).ennreal_ofReal),
      lintegral_sub_right_eq_self (fun z : Vec d => ENNReal.ofReal (cutoffRadial α r ε z)) y,
      lintegral_cutoffRadial hα0 hα1 hr hε]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ (by finiteness),
    lintegral_cutoffMass hV hr hw.aestronglyMeasurable.restrict]

/-- The complete powered seminorm estimate includes mixed pairs in both orders. -/
theorem fracSeminorm_cutoff_rpow_le {V : Set (Vec d)} (hV : IsOpen V)
    {α r ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hε : 0 < ε)
    {φ w : Vec d → ℝ} (hw : Measurable w)
    (hBound : ∀ x, |φ x| ≤ 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ euclidDist x y / ε)
    (hSep : ∀ x ∈ Function.support φ, ∀ y ∉ V, ε ≤ euclidDist x y) :
    fracSeminorm univ α r (cutoffExtension V φ w) ^ r ≤
      (2 : ℝ≥0∞) ^ r * (fracSeminorm V α r w ^ r +
        2 * (ENNReal.ofReal (ε ^ (-α * r)) *
          ENNReal.ofReal (∫ z : Vec d, cutoffRadial α r 1 z) *
            eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ^ r)) := by
  rw [fracSeminorm_rpow univ α hr, Measure.restrict_univ]
  have hi := measurable_cutoffInterior hV.measurableSet α r hw
  have he := measurable_cutoffError hV.measurableSet α r ε hw
  calc
    _ ≤ ∫⁻ xy : Vec d × Vec d, (2 : ℝ≥0∞) ^ r *
        (cutoffInterior V α r w xy + cutoffError V α r ε w xy +
          cutoffError V α r ε w xy.swap) ∂volume.prod volume :=
      lintegral_mono (cutoff_kernel_le hε hr hBound hLip hSep w)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by finiteness),
        lintegral_add_left (show Measurable (fun xy => cutoffInterior V α r w xy +
          cutoffError V α r ε w xy) from hi.add he), lintegral_add_left hi,
        lintegral_prod_swap, lintegral_cutoffInterior hV.measurableSet α hr w,
        lintegral_cutoffError hV.measurableSet hα0 hα1 hr hε hw]
      rw [two_mul, add_assoc]


/-- The source cutoff theorem, with a single dimensional constant selected
before the domain, scale, multiplier, and function. -/
theorem fractional_cutoff {α r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Set (Vec d)), IsOpen V →
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (φ w : Vec d → ℝ),
        (∀ x, |φ x| ≤ 1) →
        (∀ x y, |φ x - φ y| ≤ euclidDist x y / ε) →
        (∀ x ∈ Function.support φ, ∀ y ∉ V, ε ≤ euclidDist x y) →
        Measurable w → fracNorm V α r w < ⊤ →
        fracNorm univ α r (cutoffExtension V φ w) ≤ ENNReal.ofReal C *
          (fracSeminorm V α r w + ENNReal.ofReal (ε ^ (-α)) *
            eLpNorm w (ENNReal.ofReal r) (volume.restrict V)) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  let A : ℝ≥0∞ := ENNReal.ofReal (∫ z : Vec d, cutoffRadial α r 1 z)
  let K : ℝ≥0∞ := 1 + (2 : ℝ≥0∞) ^ r * (1 + 2 * A)
  have hKfin : K ≠ ⊤ := by dsimp only [K, A]; finiteness
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_add_right le_rfl)
  have hKreal : 0 < K.toReal := ENNReal.toReal_pos hKpos.ne' hKfin
  let C : ℝ := K.toReal ^ (1 / r)
  have hC : 0 < C := Real.rpow_pos_of_pos hKreal _
  refine ⟨C, hC, ?_⟩
  intro V hV ε hε hε1 φ w hBound hLip hSep hw _hwfin
  let L := eLpNorm w (ENNReal.ofReal r) (volume.restrict V)
  let E := ENNReal.ofReal (ε ^ (-α))
  let S := fracSeminorm V α r w
  let T := S + E * L
  have hE : 1 ≤ E := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (neg_nonpos.mpr hα0.le))
  have hscale : ENNReal.ofReal (ε ^ (-α * r)) * L ^ r = (E * L) ^ r := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
    dsimp only [E]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hε.le _) hr0.le,
      ← Real.rpow_mul hε.le]
  have hS : S ^ r ≤ T ^ r := ENNReal.rpow_le_rpow (le_add_right le_rfl) hr0.le
  have hEL : (E * L) ^ r ≤ T ^ r := ENNReal.rpow_le_rpow (le_add_left le_rfl) hr0.le
  have hL : L ≤ T := (le_mul_of_one_le_left' hE).trans (le_add_left le_rfl)
  have hφ : Measurable φ := (continuous_of_euclid_lipschitz hε hLip).measurable
  have hlp := ENNReal.rpow_le_rpow
    ((eLpNorm_cutoffExtension_le hV hφ hw hBound (ENNReal.ofReal r)).trans hL) hr0.le
  have hsem := fracSeminorm_cutoff_rpow_le hV hα0 hα1 hr0 hε hw hBound hLip hSep
  have herr : ENNReal.ofReal (ε ^ (-α * r)) * A * L ^ r ≤ A * T ^ r := by
    calc
      _ = A * (ENNReal.ofReal (ε ^ (-α * r)) * L ^ r) := by ring
      _ = A * (E * L) ^ r := by rw [hscale]
      _ ≤ _ := mul_le_mul_right hEL A
  have hp : fracNorm univ α r (cutoffExtension V φ w) ^ r ≤ K * T ^ r := by
    rw [fracNorm_rpow univ α hr0, Measure.restrict_univ]
    calc
      _ ≤ T ^ r + 2 ^ r * (S ^ r + 2 * (A * T ^ r)) :=
        add_le_add hlp (hsem.trans (mul_le_mul_right
          (add_le_add le_rfl (mul_le_mul_right herr 2)) (2 ^ r)))
      _ ≤ T ^ r + 2 ^ r * (T ^ r + 2 * (A * T ^ r)) :=
        add_le_add le_rfl (mul_le_mul_right (add_le_add hS le_rfl) (2 ^ r))
      _ = K * T ^ r := by dsimp only [K]; ring
  apply (ENNReal.rpow_le_rpow_iff hr0).1
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
  have hCr : ENNReal.ofReal C ^ r = K := by
    dsimp only [C]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hKreal.le _) hr0.le,
      ← Real.rpow_mul hKreal.le, one_div_mul_cancel hr0.ne', Real.rpow_one,
      ENNReal.ofReal_toReal hKfin]
  rw [hCr]
  exact hp

end
end CoarseDeGiorgi.Foundations.FracGeometry
