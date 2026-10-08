module

public import CoarseDeGiorgi.LowerFractional.FractionalDifference
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Jensen's two-point estimate behind `e.fractional.mean.norm`. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- Jensen for the scalar norm raised to a real exponent. -/
theorem convexOn_norm_rpow {r : ℝ} (hr : 1 ≤ r) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun x => ‖x‖ ^ r) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy s t hs ht hst
  have hn := (convexOn_norm (E := ℝ) convex_univ).2 hx hy hs ht hst
  have hp := (convexOn_rpow hr).2 (norm_nonneg x) (norm_nonneg y) hs ht hst
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (zero_le_one.trans hr)).trans hp

/-- Pointwise Jensen in the second variable, with a real source mean. -/
theorem centered_rpow_le_average {d : ℕ} {V : Set (Vec d)} {r : ℝ}
    (hr : 1 ≤ r) (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    {w : Vec d → ℝ} (hw : MemLp w (ENNReal.ofReal r) (volume.restrict V))
    (x : Vec d) :
    ‖w x - volumeAverage V w‖ₑ ^ r ≤
      ENNReal.ofReal ((volume V).toReal⁻¹) *
        ∫⁻ y in V, ‖w x - w y‖ₑ ^ r := by
  let : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVtop.lt_top⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hwi : IntegrableOn w V := hw.integrable (by simpa using ENNReal.ofReal_le_ofReal hr)
  have hp : MemLp (fun y => w x - w y) (ENNReal.ofReal r) (volume.restrict V) :=
    (memLp_const (w x)).sub hw
  have hpi : IntegrableOn (fun y => ‖w x - w y‖ ^ r) V := by
    simpa only [IntegrableOn, ENNReal.toReal_ofReal hr0.le] using
      hp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hr0).ne' ENNReal.ofReal_ne_top
  have hi : IntegrableOn (fun y => w x - w y) V := (integrable_const (w x)).sub hwi
  have hmean : (⨍ y in V, w x - w y) = w x - volumeAverage V w := by
    rw [average_eq]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    rw [integral_sub (integrable_const (w x)) hwi, setIntegral_const]
    simp only [smul_eq_mul, measureReal_def]
    unfold volumeAverage
    rw [mul_sub, ← mul_assoc,
      inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hV0, hVtop⟩), one_mul]
  have hj := (convexOn_norm_rpow hr).map_set_average_le
    ((Real.continuous_rpow_const (zero_le_one.trans hr)).comp continuous_norm).continuousOn
    isClosed_univ hV0 hVtop (Eventually.of_forall fun _ => Set.mem_univ _)
    hi hpi
  rw [hmean, average_eq] at hj
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hj
  have he := ENNReal.ofReal_le_ofReal hj
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ofReal_integral_eq_lintegral_ofReal hpi
      (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) r)] at he
  have hnorm (v : ℝ) : ENNReal.ofReal (‖v‖ ^ r) = ‖v‖ₑ ^ r := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
  simp_rw [hnorm] at he
  exact he

/-- The two-point kernel controls unweighted scalar oscillation on a set
of finite Euclidean diameter. The real division convention also covers x=y. -/
theorem oscillation_rpow_le_kernel {d : ℕ} {α r L : ℝ}
    (hr : 0 < r) (hα : 0 ≤ α) (hL : 0 < L)
    (w : Vec d → ℝ) (x y : Vec d) (hxy : euclidDist x y ≤ L) :
    ‖w x - w y‖ₑ ^ r ≤ ENNReal.ofReal (L ^ ((d : ℝ) + α * r)) *
      fracKernel α r w (x, y) := by
  by_cases he : x = y
  · subst y
    simp only [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hr]
    exact bot_le
  have hd : 0 < euclidDist x y := by
    apply Real.sqrt_pos.mpr
    exact (vecNormSq_nonneg (x - y)).lt_of_ne
      (fun hz => he (sub_eq_zero.mp (vecNormSq_eq_zero hz.symm)))
  have hexp : 0 ≤ (d : ℝ) + α * r := add_nonneg (Nat.cast_nonneg _) (mul_nonneg hα hr.le)
  have hpow := Real.rpow_le_rpow hd.le hxy hexp
  have hnum : 0 ≤ |w x - w y| ^ r := Real.rpow_nonneg (abs_nonneg _) _
  have hreal : |w x - w y| ^ r ≤
      L ^ ((d : ℝ) + α * r) *
        (|w x - w y| ^ r / euclidDist x y ^ ((d : ℝ) + α * r)) := by
    have hpos := Real.rpow_pos_of_pos hd ((d : ℝ) + α * r)
    have hc : |w x - w y| ^ r =
        euclidDist x y ^ ((d : ℝ) + α * r) *
          (|w x - w y| ^ r / euclidDist x y ^ ((d : ℝ) + α * r)) := by
      rw [mul_div_cancel₀ _ hpos.ne']
    nth_rw 1 [hc]
    exact mul_le_mul_of_nonneg_right hpow (div_nonneg hnum hpos.le)
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
  unfold fracKernel fracKernelWithDimension
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hreal)

/-- Mean plus fractional seminorm estimate, with the diameter and volume
factors kept exact. This is the finite-Lʳ form used for the smooth-core
approximation argument. -/
theorem fractional_mean_norm_of_memLp {d : ℕ} {V : Set (Vec d)} {α r L : ℝ}
    (hr : 1 ≤ r) (hα : 0 ≤ α) (hL : 0 < L) (hV : MeasurableSet V)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    (hdiam : ∀ x ∈ V, ∀ y ∈ V, euclidDist x y ≤ L)
    {w : Vec d → ℝ} (hw : MemLp w (ENNReal.ofReal r) (volume.restrict V)) :
    eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ≤
      (ENNReal.ofReal ((volume V).toReal⁻¹) *
        ENNReal.ofReal (L ^ ((d : ℝ) + α * r))) ^ (1 / r) * fracSeminorm V α r w +
      ‖volumeAverage V w‖ₑ * (volume V) ^ (1 / r) := by
  let μ := volume.restrict V
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hVtop.lt_top⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hcenter : AEStronglyMeasurable (fun x => w x - volumeAverage V w) μ :=
    hw.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hdiff : AEStronglyMeasurable (fun p : Vec d × Vec d => w p.1 - w p.2) (μ.prod μ) :=
    hw.aestronglyMeasurable.comp_fst.sub hw.aestronglyMeasurable.comp_snd
  have hJ : (∫⁻ x, ‖w x - volumeAverage V w‖ₑ ^ r ∂μ) ≤
      ENNReal.ofReal ((volume V).toReal⁻¹) *
        ∫⁻ p : Vec d × Vec d, ‖w p.1 - w p.2‖ₑ ^ r ∂μ.prod μ := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((volume V).toReal⁻¹) *
          (∫⁻ y, ‖w x - w y‖ₑ ^ r ∂μ) ∂μ :=
        lintegral_mono fun x => centered_rpow_le_average hr hV0 hVtop hw x
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_prod _ (hdiff.enorm.pow_const _)]
  have hK : (∫⁻ p : Vec d × Vec d, ‖w p.1 - w p.2‖ₑ ^ r ∂μ.prod μ) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) + α * r)) *
        ∫⁻ p : Vec d × Vec d, fracKernel α r w p ∂μ.prod μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    have hp : ∀ᵐ p ∂μ.prod μ, p.1 ∈ V ∧ p.2 ∈ V :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hV)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hV))
    filter_upwards [hp] with p hp
    exact oscillation_rpow_le_kernel hr0 hα hL w p.1 p.2 (hdiam p.1 hp.1 p.2 hp.2)
  have hbound := hJ.trans (mul_le_mul' le_rfl hK)
  have hroot := ENNReal.rpow_le_rpow hbound (div_nonneg zero_le_one hr0.le)
  have hcenterNorm : eLpNorm (fun x => w x - volumeAverage V w) (ENNReal.ofReal r) μ ≤
      (ENNReal.ofReal ((volume V).toReal⁻¹) *
        ENNReal.ofReal (L ^ ((d : ℝ) + α * r))) ^ (1 / r) * fracSeminorm V α r w := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr0).ne'
      ENNReal.ofReal_ne_top hcenter, ENNReal.toReal_ofReal hr0.le]
    unfold fracSeminorm
    simp only [ENNReal.rpow_eq_pow]
    simpa only [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one hr0.le)] using hroot
  have heq : w = (fun x => w x - volumeAverage V w) + (fun _ => volumeAverage V w) := by
    funext x
    exact (sub_add_cancel _ _).symm
  have htri := eLpNorm_add_le (f := fun x => w x - volumeAverage V w)
    (g := fun _ => volumeAverage V w) (μ := μ) (p := ENNReal.ofReal r)
    (by simpa using ENNReal.ofReal_le_ofReal hr)
  rw [← heq] at htri
  refine htri.trans (add_le_add hcenterNorm ?_)
  rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hr0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr0.le]
  simp only [μ, Measure.restrict_apply_univ, le_refl]

/-- A measurable function with finite fractional seminorm on a bounded
positive-volume set belongs to Lʳ. No Lʳ premise is used. -/
theorem memLp_of_fracSeminorm_lt_top {d : ℕ} {V : Set (Vec d)} {α r L : ℝ}
    (hr : 0 < r) (hα : 0 ≤ α) (hL : 0 < L) (hV : MeasurableSet V)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    (hdiam : ∀ x ∈ V, ∀ y ∈ V, euclidDist x y ≤ L)
    {w : Vec d → ℝ} (hw : AEStronglyMeasurable w (volume.restrict V))
    (hsemi : fracSeminorm V α r w < ⊤) :
    MemLp w (ENNReal.ofReal r) (volume.restrict V) := by
  let μ := volume.restrict V
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hVtop.lt_top⟩
  let : NeZero (volume V) := ⟨hV0⟩
  have hfrac : MemLp (fractionalDifference α r w) (ENNReal.ofReal r) (μ.prod μ) := by
    change eLpNorm (fractionalDifference α r w) (ENNReal.ofReal r) (μ.prod μ) < ⊤
    rw [← fracSeminorm_eq_eLpNorm hr hw]
    exact hsemi
  have hpow : Integrable (fun p : Vec d × Vec d =>
      ‖fractionalDifference α r w p‖ ^ r) (μ.prod μ) := by
    simpa only [ENNReal.toReal_ofReal hr.le] using
      hfrac.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
  have hdiffM : AEStronglyMeasurable (fun p : Vec d × Vec d => w p.1 - w p.2) (μ.prod μ) :=
    hw.comp_fst.sub hw.comp_snd
  have hdiffpow : Integrable (fun p : Vec d × Vec d => ‖w p.1 - w p.2‖ ^ r) (μ.prod μ) := by
    refine (hpow.const_mul (L ^ ((d : ℝ) + α * r))).mono'
      (hdiffM.norm.aemeasurable.pow_const _).aestronglyMeasurable ?_
    have hp : ∀ᵐ p ∂μ.prod μ, p.1 ∈ V ∧ p.2 ∈ V :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hV)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hV))
    filter_upwards [hp] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
    have he := oscillation_rpow_le_kernel hr hα hL w p.1 p.2
      (hdiam p.1 hp.1 p.2 hp.2)
    rw [fracKernel_eq_fractionalDifference α hr w p, ← ofReal_norm, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)] at he
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) r),
      ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hL.le _)
        (Real.rpow_nonneg (norm_nonneg _) r))] at hh
    exact hh
  obtain ⟨y, hy⟩ := hdiffpow.prod_left_ae.exists
  have hrow : MemLp (fun x => w x - w y) (ENNReal.ofReal r) μ := by
    apply (integrable_norm_rpow_iff (f := fun x => w x - w y)
      (hw.sub aestronglyMeasurable_const)
      (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hr.le] using hy
  have hsum := hrow.add (memLp_const (w y))
  have heq : (fun x => w x - w y) + (fun _ => w y) = w := by
    funext x
    exact sub_add_cancel _ _
  rw [heq] at hsum
  exact hsum

/-- The full extended mean-plus-seminorm inequality for any a.e.-measurable
scalar function, including the infinite-seminorm case. -/
theorem fractional_mean_norm {d : ℕ} {V : Set (Vec d)} {α r L : ℝ}
    (hr : 1 ≤ r) (hα : 0 ≤ α) (hL : 0 < L) (hV : MeasurableSet V)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    (hdiam : ∀ x ∈ V, ∀ y ∈ V, euclidDist x y ≤ L)
    {w : Vec d → ℝ} (hw : AEStronglyMeasurable w (volume.restrict V)) :
    eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ≤
      (ENNReal.ofReal ((volume V).toReal⁻¹) *
        ENNReal.ofReal (L ^ ((d : ℝ) + α * r))) ^ (1 / r) * fracSeminorm V α r w +
      ‖volumeAverage V w‖ₑ * (volume V) ^ (1 / r) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  by_cases hsemi : fracSeminorm V α r w < ⊤
  · exact fractional_mean_norm_of_memLp hr hα hL hV hV0 hVtop hdiam
      (memLp_of_fracSeminorm_lt_top hr0 hα hL hV hV0 hVtop hdiam hw hsemi)
  · have he : fracSeminorm V α r w = ⊤ := not_lt_top_iff.mp hsemi
    rw [he, ENNReal.mul_top (by
      apply (ENNReal.rpow_pos_of_nonneg _ (div_nonneg zero_le_one hr0.le)).ne'
      exact pos_iff_ne_zero.mpr (mul_ne_zero
        (ENNReal.ofReal_pos.mpr (inv_pos.mpr (ENNReal.toReal_pos hV0 hVtop))).ne'
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hL _)).ne')), top_add]
    exact le_top


end CoarseDeGiorgi.LowerFractional
