module

public import CoarseDeGiorgi.Statements.OriginCube
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar infrastructure for the Appendix B logarithm-to-integral lemma. -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Scalar

open Homogenization MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

private theorem scalar_l1_eq_ofReal_integral_abs {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ x, |f x| ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.1]
  simpa only [← ofReal_norm, Real.norm_eq_abs] using
    (ofReal_integral_eq_lintegral_ofReal hf.norm
      (Eventually.of_forall fun x => norm_nonneg (f x))).symm

/-- The cube `originCube ρ` is the product of the intervals `(-ρ/2, ρ/2)`. -/
theorem originCube_eq_pi_Ioo {d : ℕ} (ρ : ℝ) :
    CoarseDeGiorgi.originCube (d := d) ρ =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(ρ / 2)) (ρ / 2)) := by
  ext x
  simp [CoarseDeGiorgi.originCube, Set.mem_pi]

/-- The unit cube `originCube 1` has volume one. -/
theorem volume_originCube_one {d : ℕ} :
    volume (CoarseDeGiorgi.originCube (d := d) 1) = 1 := by
  rw [originCube_eq_pi_Ioo, Real.volume_pi_Ioo]
  norm_num

/-- The cube `originCube ρ` has volume `ρ ^ d`. -/
theorem volume_originCube_eq {d : ℕ} {ρ : ℝ} :
    volume (CoarseDeGiorgi.originCube (d := d) ρ) = (ENNReal.ofReal ρ) ^ d := by
  rw [originCube_eq_pi_Ioo, Real.volume_pi_Ioo]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  congr 1
  ring

/-- `originCube ρ ⊆ originCube 1` for `ρ ≤ 1`. -/
theorem originCube_subset_of_le_one {d : ℕ} {ρ : ℝ} (hρ : ρ ≤ 1) :
    CoarseDeGiorgi.originCube (d := d) ρ ⊆ CoarseDeGiorgi.originCube 1 := by
  intro x hx i
  rcases hx i with ⟨hl, hu⟩
  constructor <;> linarith

/-- `originCube ρ` has volume at most one for `ρ ≤ 1`. -/
theorem volume_originCube_le_one {d : ℕ} {ρ : ℝ} (hρ : ρ ≤ 1) :
    volume (CoarseDeGiorgi.originCube (d := d) ρ) ≤ 1 := by
  calc
    volume (CoarseDeGiorgi.originCube ρ) ≤ volume (CoarseDeGiorgi.originCube 1) :=
      measure_mono (originCube_subset_of_le_one hρ)
    _ = 1 := volume_originCube_one

/-- `originCube ρ` is measurable. -/
theorem measurableSet_originCube {d : ℕ} (ρ : ℝ) :
    MeasurableSet (CoarseDeGiorgi.originCube (d := d) ρ) := by
  have hopen : IsOpen (CoarseDeGiorgi.originCube (d := d) ρ) := by
    change IsOpen {x : Vec d | ∀ i, x i ∈ Set.Ioo (-(ρ / 2)) (ρ / 2)}
    simp only [← Set.iInter_ofPred]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_Ioo.preimage (continuous_apply i)
  exact hopen.measurableSet

/-- `originCube ρ` has positive volume for `ρ > 0`. -/
theorem volume_originCube_pos {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    0 < volume (CoarseDeGiorgi.originCube (d := d) ρ) := by
  rw [volume_originCube_eq]
  apply (pos_iff_ne_zero).2
  exact pow_ne_zero d (ENNReal.ofReal_pos.mpr hρ).ne'

/-- The cubes `originCube ρ` increase with `ρ`. -/
theorem originCube_subset_of_le {d : ℕ} {ρ R : ℝ} (hρR : ρ ≤ R) :
    CoarseDeGiorgi.originCube (d := d) ρ ⊆ CoarseDeGiorgi.originCube R := by
  intro x hx i
  rcases hx i with ⟨hl, hu⟩
  constructor <;> linarith

/-- The adaptive exponent in `l.bombieri`: for `F > 3A > 0` there is `0 < b < 1` with
`(1 - b) log (F / (3A)) = b F`. -/
theorem adaptive_exponent (F A : ℝ) (hA : 0 < A) (hF : 3 * A < F) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      (1 - b) * Real.log (F / (3 * A)) = b * F := by
  have hq : 1 < F / (3 * A) := by
    rw [one_lt_div (by positivity)]
    linarith
  have hl : 0 < Real.log (F / (3 * A)) := Real.log_pos hq
  let b := Real.log (F / (3 * A)) /
    (Real.log (F / (3 * A)) + F)
  have hden : 0 < Real.log (F / (3 * A)) + F := by
    have hFpos : 0 < F := by linarith
    linarith
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos hl hden
  have hb1 : b < 1 := by
    dsimp [b]
    exact (div_lt_one hden).2 (by linarith)
  refine ⟨b, hb, hb1, ?_⟩
  dsimp [b]
  field_simp [ne_of_gt hden]
  ring

/-- The adaptive exponent satisfies `1 / b = 1 + F / log (F / (3A))`. -/
theorem adaptive_exponent_inverse {F A b : ℝ} (hA : 0 < A) (hF : 3 * A < F)
    (hb : 0 < b)
    (hbal : (1 - b) * Real.log (F / (3 * A)) = b * F) :
    1 / b = 1 + F / Real.log (F / (3 * A)) := by
  have hL : 0 < Real.log (F / (3 * A)) := by
    exact Real.log_pos ((one_lt_div (by positivity)).2 hF)
  have hmul : b * (F + Real.log (F / (3 * A))) = Real.log (F / (3 * A)) := by
    nlinarith [hbal]
  calc
    1 / b = (F + Real.log (F / (3 * A))) / Real.log (F / (3 * A)) := by
      field_simp [ne_of_gt hb, ne_of_gt hL]
      nlinarith [hmul]
    _ = 1 + F / Real.log (F / (3 * A)) := by
      field_simp [ne_of_gt hL]
      ring

/-- `(2 A δ ^ (-ξ)) ^ 6 = (2 A) ^ 6 δ ^ (-6 ξ)` for `δ ≥ 0`. -/
theorem bombieri_scale_power_six {A δ ξ : ℝ} (hδ : 0 ≤ δ) :
    (2 * A * δ ^ (-ξ)) ^ 6 = (2 * A) ^ 6 * δ ^ (-6 * ξ) := by
  rw [mul_pow, ← Real.rpow_natCast (δ ^ (-ξ)) 6, ← Real.rpow_mul hδ]
  congr 1
  ring_nf

/-- Arithmetic of the large case of the one-step inequality in `l.bombieri`:
`F / 3 + (1 / b) log x ≤ F / 2 + 3 A x ^ 6`. -/
theorem bombieri_large_threshold_arithmetic {F A x b L : ℝ}
    (hA : 1 ≤ A) (hF : 0 ≤ F) (hL : 0 < L)
    (hlogbound : Real.log x ≤ x ^ 6)
    (hratio : Real.log x / L ≤ 1 / 6)
    (hbal : 1 / b = 1 + F / L) :
    F / 3 + (1 / b) * Real.log x ≤ F / 2 + 3 * A * x ^ 6 := by
  have hprod : (F / L) * Real.log x ≤ F / 6 := by
    calc
      (F / L) * Real.log x = F * (Real.log x / L) := by
        field_simp [ne_of_gt hL]
      _ ≤ F * (1 / 6) := mul_le_mul_of_nonneg_left hratio hF
      _ = F / 6 := by ring
  have hterm : (1 / b) * Real.log x ≤ Real.log x + F / 6 := by
    rw [hbal]
    calc
      (1 + F / L) * Real.log x = Real.log x + (F / L) * Real.log x := by ring
      _ ≤ Real.log x + F / 6 := add_le_add le_rfl hprod
  have hcost : Real.log x ≤ 3 * A * x ^ 6 := by
    calc
      Real.log x ≤ x ^ 6 := hlogbound
      _ ≤ 3 * A * x ^ 6 := by
        have hthree : 1 ≤ 3 * A := by nlinarith [hA]
        simpa using mul_le_mul_of_nonneg_right (a := x ^ 6) hthree (by positivity)
  calc
    F / 3 + (1 / b) * Real.log x ≤ F / 3 + (Real.log x + F / 6) :=
      add_le_add le_rfl hterm
    _ = F / 3 + Real.log x + F / 6 := by ring
    _ ≤ F / 2 + 3 * A * x ^ 6 := by nlinarith [hF, hcost]

/-- `log x ≤ x ^ 6` for `x ≥ 1`. -/
theorem log_le_sixth_power {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x ^ 6 := by
  have hlog : Real.log x ≤ x := by
    calc
      Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
      _ ≤ x := by linarith
  have hxpow : x ≤ x ^ 6 := by
    calc
      x = x * 1 := by ring
      _ ≤ x * x ^ 5 := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ hx) (by linarith)
      _ = x ^ 6 := by ring
  exact hlog.trans hxpow

/-- `1 ≤ x ^ (-ξ)` for `0 < x ≤ 1` and `ξ > 0`. -/
theorem one_le_rpow_neg {x ξ : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hξ : 0 < ξ) :
    1 ≤ x ^ (-ξ) := by
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log x ≤ 0 := by
    calc
      Real.log x ≤ Real.log 1 := Real.log_le_log hx0 hx1
      _ = 0 := Real.log_one
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (show -ξ ≤ 0 by linarith) hlog]

/-- A function measurable on `originCube (7/8)` is a.e.-measurable on every smaller
`originCube ρ`. -/
theorem aemeasurable_on_smaller_originCube {d : ℕ} {v : Vec d → ℝ}
    (hv : Measurable (fun x : CoarseDeGiorgi.originCube (d := d) (7 / 8) => v x))
    {ρ : ℝ} (hρ : ρ ≤ 7 / 8) :
    AEMeasurable v (volume.restrict (CoarseDeGiorgi.originCube ρ)) := by
  let E := CoarseDeGiorgi.originCube (d := d) (7 / 8)
  let V := CoarseDeGiorgi.originCube (d := d) ρ
  obtain ⟨w, hw, hEq⟩ :=
    ((MeasurableEmbedding.subtype_coe
      (measurableSet_originCube (d := d) (7 / 8))).exists_measurable_extend
        hv (fun _ => ⟨0⟩))
  have hsub : V ⊆ E := originCube_subset_of_le hρ
  have haeq : v =ᵐ[volume.restrict V] w := by
    filter_upwards [ae_restrict_mem (measurableSet_originCube (d := d) ρ)] with x hx
    have hEqx := congrFun hEq ⟨x, hsub hx⟩
    simpa [Function.comp_apply] using hEqx.symm
  exact hw.aemeasurable.congr haeq.symm

/-- A function measurable on `originCube (7/8)` agrees there with a measurable function on
`Vec d`. -/
theorem exists_measurable_extension_originCube {d : ℕ} {v : Vec d → ℝ}
    (hv : Measurable (fun x : CoarseDeGiorgi.originCube (d := d) (7 / 8) => v x)) :
    ∃ w : Vec d → ℝ, Measurable w ∧
      ∀ x ∈ CoarseDeGiorgi.originCube (d := d) (7 / 8), w x = v x := by
  obtain ⟨w, hw, hEq⟩ :=
    ((MeasurableEmbedding.subtype_coe
      (measurableSet_originCube (d := d) (7 / 8))).exists_measurable_extend
        hv (fun _ => ⟨0⟩))
  refine ⟨w, hw, ?_⟩
  intro x hx
  have hEqx := congrFun hEq ⟨x, hx⟩
  simpa [Function.comp_apply] using hEqx

/-- The `L¹` bound on `log v` over `originCube (7/8)` restricts to every smaller `originCube ρ`. -/
theorem log_lintegral_bound_on_cube {d : ℕ} {v : Vec d → ℝ}
    (hv : Measurable (fun x : CoarseDeGiorgi.originCube (d := d) (7 / 8) => v x))
    {A₁ : ℝ}
    (hlog : eLpNorm (fun x => Real.log (v x)) 1
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) (7 / 8))) ≤ ENNReal.ofReal A₁)
    {ρ : ℝ} (hρ : ρ ≤ 7 / 8) :
    ∫⁻ x, ENNReal.ofReal (|Real.log (v x)|) ∂
      (volume.restrict (CoarseDeGiorgi.originCube ρ)) ≤ ENNReal.ofReal A₁ := by
  have hsub : CoarseDeGiorgi.originCube (d := d) ρ ⊆
      CoarseDeGiorgi.originCube (d := d) (7 / 8) := originCube_subset_of_le hρ
  have hμ : volume.restrict (CoarseDeGiorgi.originCube ρ) ≤
      volume.restrict (CoarseDeGiorgi.originCube (7 / 8)) :=
    Measure.restrict_mono hsub le_rfl
  have hvρ := aemeasurable_on_smaller_originCube hv hρ
  have hlogρ : AEMeasurable (fun x => Real.log (v x))
      (volume.restrict (CoarseDeGiorgi.originCube ρ)) :=
    Real.measurable_log.comp_aemeasurable hvρ
  have hnorm := (eLpNorm_mono_measure (fun x => Real.log (v x)) hμ).trans hlog
  rw [eLpNorm_one_eq_lintegral_enorm hlogρ.aestronglyMeasurable] at hnorm
  simpa only [Real.enorm_eq_ofReal_abs] using hnorm

/-- Chebyshev bound in `l.bombieri`: `{log v > f / 3}` has measure at most `A₁ / (f / 3)` in
`originCube ρ`. -/
theorem log_tail_measure_bound {d : ℕ} {v : Vec d → ℝ}
    (hv : Measurable (fun x : CoarseDeGiorgi.originCube (d := d) (7 / 8) => v x))
    {A₁ f ρ : ℝ} (hA₁ : 0 ≤ A₁) (hf : 3 * A₁ < f) (hρ : ρ ≤ 7 / 8)
    (hlog : eLpNorm (fun x => Real.log (v x)) 1
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) (7 / 8))) ≤ ENNReal.ofReal A₁) :
    volume.restrict (CoarseDeGiorgi.originCube ρ)
      {x | f / 3 < Real.log (v x)} ≤ ENNReal.ofReal A₁ / ENNReal.ofReal (f / 3) := by
  let μ := volume.restrict (CoarseDeGiorgi.originCube (d := d) ρ)
  have hlogμ := log_lintegral_bound_on_cube hv hlog hρ
  have hlogmeas : AEMeasurable (fun x => Real.log (v x)) μ :=
    Real.measurable_log.comp_aemeasurable (aemeasurable_on_smaller_originCube hv hρ)
  let g : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (|Real.log (v x)|)
  have habs : AEMeasurable (fun x => |Real.log (v x)|) μ := by
    convert measurable_norm.comp_aemeasurable hlogmeas using 1
    ext x
    simp [Real.norm_eq_abs]
  have hg : AEMeasurable g μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable habs
  have hε : ENNReal.ofReal (f / 3) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hεtop : ENNReal.ofReal (f / 3) ≠ ∞ := ENNReal.ofReal_ne_top
  have hset : {x : Vec d | f / 3 < Real.log (v x)} ⊆
      {x | ENNReal.ofReal (f / 3) ≤ g x} := by
    intro x hx
    change f / 3 < Real.log (v x) at hx
    change ENNReal.ofReal (f / 3) ≤ ENNReal.ofReal (|Real.log (v x)|)
    apply ENNReal.ofReal_le_ofReal
    have hnonneg : 0 ≤ Real.log (v x) := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  calc
    μ {x | f / 3 < Real.log (v x)} ≤ μ {x | ENNReal.ofReal (f / 3) ≤ g x} :=
      measure_mono hset
    _ ≤ (∫⁻ x, g x ∂μ) / ENNReal.ofReal (f / 3) :=
      meas_ge_le_lintegral_div hg hε hεtop
    _ ≤ ENNReal.ofReal A₁ / ENNReal.ofReal (f / 3) := by
      gcongr

/-- Chebyshev bound in `l.bombieri`: `{log v > f / 3}` has measure at most `3 A₁ / f` in
`originCube ρ`. -/
theorem log_tail_measure_bound_real {d : ℕ} {v : Vec d → ℝ}
    (hv : Measurable (fun x : CoarseDeGiorgi.originCube (d := d) (7 / 8) => v x))
    {A₁ f ρ : ℝ} (hA₁ : 0 ≤ A₁) (hf : 3 * A₁ < f) (hρ : ρ ≤ 7 / 8)
    (hlog : eLpNorm (fun x => Real.log (v x)) 1
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) (7 / 8))) ≤ ENNReal.ofReal A₁) :
    volume.restrict (CoarseDeGiorgi.originCube ρ)
      {x | f / 3 < Real.log (v x)} ≤ ENNReal.ofReal (3 * A₁ / f) := by
  have hbase := log_tail_measure_bound hv hA₁ hf hρ hlog
  have hden : 0 < f / 3 := by linarith
  have heq : ENNReal.ofReal A₁ / ENNReal.ofReal (f / 3) =
      ENNReal.ofReal (3 * A₁ / f) := by
    rw [← ENNReal.ofReal_div_of_pos hden]
    congr 1
    field_simp
  exact hbase.trans_eq heq

/-- Hölder's inequality for a power `0 < b < 1`: `∫_s F ^ b ≤ (∫_s F) ^ b μ(s) ^ (1 - b)`. -/
theorem lintegral_rpow_restrict_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (_hs : MeasurableSet s) {F : α → ℝ≥0∞} (hF : AEMeasurable F μ)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∫⁻ x in s, F x ^ b ∂μ) ≤
      (∫⁻ x in s, F x ∂μ) ^ b * (μ s) ^ (1 - b) := by
  have hh := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ.restrict s) (f := F) (g := fun _ => (1 : ℝ≥0∞))
    (p := b) (q := 1 - b) (hF.restrict) aemeasurable_const
    (le_of_lt hb0) (by linarith) (by ring)
  simpa [Measure.restrict_apply, ENNReal.one_rpow] using hh

/-- With the adaptive exponent, `(exp F) ^ b (3A / F) ^ (1 - b) = 1`. -/
theorem adaptive_tail_product_eq_one {A F b : ℝ}
    (hA : 0 < A) (hF : 3 * A < F) (hb : 0 < b) (hb1 : b < 1)
    (hbal : (1 - b) * Real.log (F / (3 * A)) = b * F) :
    (ENNReal.ofReal (Real.exp F)) ^ b *
      (ENNReal.ofReal (3 * A / F)) ^ (1 - b) = 1 := by
  have hratio : 3 * A / F = (F / (3 * A))⁻¹ := by
    field_simp
  have hFpos : 0 < F := by linarith
  have hq : 0 < F / (3 * A) := div_pos hFpos (by positivity)
  have hy : 0 < 3 * A / F := div_pos (by positivity) hFpos
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos F).le hb.le,
    ENNReal.ofReal_rpow_of_nonneg (le_of_lt hy) (by linarith : 0 ≤ 1 - b),
    ← ENNReal.ofReal_mul (by positivity)]
  have hreal : Real.exp F ^ b * (3 * A / F) ^ (1 - b) = 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos F), Real.log_exp,
      Real.rpow_def_of_pos hy, hratio, Real.log_inv]
    rw [← Real.exp_add]
    have hz : F * b + -Real.log (F / (3 * A)) * (1 - b) = 0 := by
      nlinarith [hbal]
    rw [hz, Real.exp_zero]
  rw [hreal]
  norm_num

/-- Split of `∫ v ^ b` over `{log v > F / 3}` and its complement in `l.bombieri`:
`∫ v ^ b ≤ 2 exp (b F / 3)`. -/
theorem log_power_integral_split {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : α → ℝ} (hv : Measurable v) (hpos : ∀ᵐ x ∂μ, 0 < v x)
    {A F b : ℝ} (hA : 0 < A) (hF : 3 * A < F) (hb : 0 < b) (hb1 : b < 1)
    (hbal : (1 - b) * Real.log (F / (3 * A)) = b * F)
    (hmass : μ Set.univ ≤ 1)
    (hV : ∫⁻ x, ENNReal.ofReal (v x) ∂μ ≤ ENNReal.ofReal (Real.exp F))
    (hE : μ {x | F / 3 < Real.log (v x)} ≤ ENNReal.ofReal (3 * A / F)) :
    ∫⁻ x, (ENNReal.ofReal (v x)) ^ b ∂μ ≤
      ENNReal.ofReal (2 * Real.exp (b * F / 3)) := by
  let E : Set α := {x | F / 3 < Real.log (v x)}
  let V : α → ℝ≥0∞ := fun x => ENNReal.ofReal (v x)
  let I : α → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hEmeas : MeasurableSet E :=
    measurableSet_lt measurable_const (Real.measurable_log.comp hv)
  have hVmeas : Measurable V := ENNReal.continuous_ofReal.measurable.comp hv
  have hImeas : Measurable I := measurable_const.indicator hEmeas
  have hpt : (fun x => V x ^ b) ≤ᵐ[μ] (fun x => ENNReal.ofReal (Real.exp (b * F / 3)) +
      V x ^ b * I x) := by
    filter_upwards [hpos] with x hx
    by_cases hxE : x ∈ E
    · have hI : I x = 1 := by simp [I, hxE]
      have hle : V x ^ b ≤ ENNReal.ofReal (Real.exp (b * F / 3)) + V x ^ b :=
        le_add_of_nonneg_left (a := V x ^ b)
          (b := ENNReal.ofReal (Real.exp (b * F / 3))) bot_le
      simp [I, hxE]
    · have hlog : Real.log (v x) ≤ F / 3 := le_of_not_gt hxE
      have hpow : V x ^ b = ENNReal.ofReal (Real.exp (b * Real.log (v x))) := by
        dsimp [V]
        rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hx) (le_of_lt hb),
          Real.rpow_def_of_pos hx]
        exact congrArg ENNReal.ofReal (congrArg Real.exp (by ring))
      have hle : Real.exp (b * Real.log (v x)) ≤ Real.exp (b * F / 3) := by
        apply Real.exp_le_exp.mpr
        have hbF : 0 ≤ b := le_of_lt hb
        nlinarith
      have hc : V x ^ b ≤ ENNReal.ofReal (Real.exp (b * F / 3)) := by
        rw [hpow]
        exact ENNReal.ofReal_le_ofReal hle
      simpa [I, hxE] using hc
  have hsplit :
      (∫⁻ x, V x ^ b ∂μ) ≤
        ENNReal.ofReal (Real.exp (b * F / 3)) * μ Set.univ +
          ∫⁻ x in E, V x ^ b ∂μ := by
    calc
      (∫⁻ x, V x ^ b ∂μ) ≤
          ∫⁻ x, ENNReal.ofReal (Real.exp (b * F / 3)) + V x ^ b * I x ∂μ :=
        lintegral_mono_ae hpt
      _ = ENNReal.ofReal (Real.exp (b * F / 3)) * μ Set.univ +
          ∫⁻ x in E, V x ^ b ∂μ := by
        rw [lintegral_add_left' aemeasurable_const, lintegral_const]
        have hIeq : (fun x => V x ^ b * I x) = E.indicator (fun x => V x ^ b) := by
          funext x
          by_cases hx : x ∈ E <;> simp [I, hx]
        rw [hIeq, lintegral_indicator hEmeas]
  have hholder := lintegral_rpow_restrict_le (μ := μ) hEmeas hVmeas.aemeasurable hb hb1
  have htail : (∫⁻ x in E, V x ^ b ∂μ) ≤ 1 := by
    calc
      (∫⁻ x in E, V x ^ b ∂μ) ≤
          (∫⁻ x in E, V x ∂μ) ^ b * (μ E) ^ (1 - b) := hholder
      _ ≤ (ENNReal.ofReal (Real.exp F)) ^ b *
          (ENNReal.ofReal (3 * A / F)) ^ (1 - b) := by
        gcongr
        · exact (setLIntegral_le_lintegral E V).trans hV
      _ = 1 := adaptive_tail_product_eq_one hA hF hb hb1 hbal
  have hconstant : ENNReal.ofReal (Real.exp (b * F / 3)) * μ Set.univ ≤
      ENNReal.ofReal (Real.exp (b * F / 3)) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (b * F / 3)) * 1 := by gcongr
      _ = _ := by simp
  have hexp : 1 ≤ Real.exp (b * F / 3) := by
    apply Real.one_le_exp_iff.mpr
    have hFpos : 0 < F := by linarith
    positivity
  have hsum := add_le_add hconstant htail
  have hfinal : (∫⁻ x, V x ^ b ∂μ) ≤
      ENNReal.ofReal (2 * Real.exp (b * F / 3)) := by
   calc
    (∫⁻ x, V x ^ b ∂μ) ≤
        ENNReal.ofReal (Real.exp (b * F / 3)) + 1 := hsplit.trans hsum
    _ ≤ ENNReal.ofReal (2 * Real.exp (b * F / 3)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
      all_goals norm_num
  simpa [V] using hfinal

/-- For positive `v`, `‖v‖_{L^b} ^ b = ∫ v ^ b`. -/
theorem eLpNorm_rpow_eq_lintegral_ofReal {d : ℕ} {μ : Measure (Vec d)}
    {v : Vec d → ℝ} (hv : Measurable v) (hpos : ∀ᵐ x ∂μ, 0 < v x)
    {b : ℝ} (hb : 0 < b) :
    eLpNorm v (ENNReal.ofReal b) μ ^ b =
      ∫⁻ x, (ENNReal.ofReal (v x)) ^ b ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top hv.aestronglyMeasurable,
    ENNReal.toReal_ofReal hb.le]
  rw [← ENNReal.rpow_mul]
  have hpow : (1 / b) * b = 1 := by field_simp
  rw [hpow, ENNReal.rpow_one]
  apply lintegral_congr_ae
  filter_upwards [hpos] with x hx
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos hx]

/-- The bound `∫ v ^ b ≤ 2 exp (b F / 3)` gives `‖v‖_{L^b} ≤ 2 ^ (1 / b) exp (F / 3)`. -/
theorem eLpNorm_subunit_bound {d : ℕ} {μ : Measure (Vec d)} {v : Vec d → ℝ}
    (hv : Measurable v) (hpos : ∀ᵐ x ∂μ, 0 < v x) {F b : ℝ}
    (hb : 0 < b) (hbound :
      ∫⁻ x, (ENNReal.ofReal (v x)) ^ b ∂μ ≤
        ENNReal.ofReal (2 * Real.exp (b * F / 3))) :
    eLpNorm v (ENNReal.ofReal b) μ ≤
      ENNReal.ofReal (2 ^ (1 / b) * Real.exp (F / 3)) := by
  have hpow := eLpNorm_rpow_eq_lintegral_ofReal hv hpos hb
  have hpowbound : eLpNorm v (ENNReal.ofReal b) μ ^ b ≤
      ENNReal.ofReal (2 * Real.exp (b * F / 3)) := hpow.trans_le hbound
  have hroot : eLpNorm v (ENNReal.ofReal b) μ ≤
      (ENNReal.ofReal (2 * Real.exp (b * F / 3))) ^ (1 / b) := by
    calc
      eLpNorm v (ENNReal.ofReal b) μ =
          (eLpNorm v (ENNReal.ofReal b) μ ^ b) ^ (1 / b) := by
        rw [← ENNReal.rpow_mul]
        have he : b * (1 / b) = 1 := by field_simp
        rw [he, ENNReal.rpow_one]
      _ ≤ _ := ENNReal.rpow_le_rpow hpowbound (by positivity)
  have hreal : (2 * Real.exp (b * F / 3)) ^ (1 / b) =
      2 ^ (1 / b) * Real.exp (F / 3) := by
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    congr 1
    field_simp
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity : 0 ≤ 1 / b),
    hreal] at hroot
  exact hroot

/-- For a nonnegative integrable `v`, `‖v‖_{L¹} = ∫ v`. -/
theorem eLpNorm_one_eq_ofReal_integral {d : ℕ} {μ : Measure (Vec d)}
    {v : Vec d → ℝ} (hint : Integrable v μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ v x) :
    eLpNorm v 1 μ = ENNReal.ofReal (∫ x, v x ∂μ) := by
  rw [scalar_l1_eq_ofReal_integral_abs hint]
  congr 1
  exact integral_congr_ae (hnonneg.mono fun x hx => abs_of_nonneg hx)

end
end CoarseDeGiorgi.Harnack.Scalar
