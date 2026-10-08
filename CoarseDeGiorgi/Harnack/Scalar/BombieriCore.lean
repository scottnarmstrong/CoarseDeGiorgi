module

public import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas
public import CoarseDeGiorgi.Harnack.Scalar.BombieriIteration

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Scalar

open Filter Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

private def bombieriMass {d : ℕ} (v : Vec d → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x, v x ∂(volume.restrict (CoarseDeGiorgi.originCube ρ))

private def bombieriEnvelope {d : ℕ} (v : Vec d → ℝ) (ρ : ℝ) : ℝ :=
  max 0 (Real.log (bombieriMass v ρ))

/-- Lemma `l.bombieri`, stated for a function `v` measurable on all of `Vec d`. -/
theorem bombieri_integral_bound_global (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (A₁ A₂ : ℝ), 1 ≤ A₁ → 1 ≤ A₂ →
        ∀ v : Vec d → ℝ,
          Measurable v →
          (∀ᵐ x ∂(volume.restrict (CoarseDeGiorgi.originCube (d := d) (7 / 8))), 0 < v x) →
          IntegrableOn v (CoarseDeGiorgi.originCube (7 / 8)) →
          eLpNorm (fun x => Real.log (v x)) 1
            (volume.restrict (CoarseDeGiorgi.originCube (7 / 8))) ≤ ENNReal.ofReal A₁ →
          (∀ b : ℝ, 0 < b → b < 1 →
            ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
              eLpNorm v 1 (volume.restrict (CoarseDeGiorgi.originCube ρ)) ≤
                (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) *
                  eLpNorm v (ENNReal.ofReal b) (volume.restrict (CoarseDeGiorgi.originCube R))) →
          eLpNorm v 1 (volume.restrict (CoarseDeGiorgi.originCube (3 / 4))) ≤
            ENNReal.ofReal (Real.exp (C * A₁ * A₂ ^ 6)) := by
  obtain ⟨hratio0, hratio1⟩ := bombieri_series_ratio_bounds
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : -(Real.log 2) / (12 * ξ) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hlog2) (by positivity)
  have hq : bombieriRadiusRatio ξ < 1 := (Real.exp_lt_one_iff).2 harg
  let C := 192 * (8 / (1 - bombieriRadiusRatio ξ)) ^ (6 * ξ) *
    (1 - bombieriSeriesRatio)⁻¹
  have hC : 0 < C := by
    dsimp [C]
    have hden : 0 < 1 - bombieriRadiusRatio ξ := by linarith
    have hbase : 0 < 8 / (1 - bombieriRadiusRatio ξ) := by positivity
    have hseries : 0 < 1 - bombieriSeriesRatio := by linarith
    positivity
  refine ⟨C, hC, ?_⟩
  intro d A₁ A₂ hA₁ hA₂ v hv hpos hvint hlog hrev
  let μ₀ : Measure (Vec d) := volume.restrict (CoarseDeGiorgi.originCube (d := d) (7 / 8))
  have hvint₀ : Integrable v μ₀ := by
    change Integrable v (volume.restrict (CoarseDeGiorgi.originCube (d := d) (7 / 8)))
    exact hvint
  have hnonneg₀ : ∀ᵐ x ∂μ₀, 0 ≤ v x := hpos.mono fun _ hx => hx.le
  have hmeasSubtype : Measurable
      (fun x : CoarseDeGiorgi.originCube (d := d) (7 / 8) => v x) :=
    hv.comp measurable_subtype_coe
  have hIpositive : ∀ ρ, 3 / 4 ≤ ρ → ρ ≤ 7 / 8 → 0 < bombieriMass v ρ := by
    intro ρ hρ hρtop
    let μρ : Measure (Vec d) := volume.restrict (CoarseDeGiorgi.originCube ρ)
    have hsubset : CoarseDeGiorgi.originCube (d := d) ρ ⊆
        CoarseDeGiorgi.originCube (d := d) (7 / 8) := originCube_subset_of_le hρtop
    have hμρ₀ : μρ ≤ μ₀ := by
      dsimp [μρ, μ₀]
      exact Measure.restrict_mono hsubset le_rfl
    have hIntρ : Integrable v μρ := hvint₀.mono_measure hμρ₀
    have hposρ : ∀ᵐ x ∂μρ, 0 < v x := hpos.filter_mono (ae_mono hμρ₀)
    have hnonnegρ : ∀ᵐ x ∂μρ, 0 ≤ v x := hposρ.mono fun _ hx => hx.le
    let V : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (v x)
    have hVmeas : Measurable V := ENNReal.continuous_ofReal.measurable.comp hv
    have hsupport : (Set.univ : Set (Vec d)) ≤ᵐ[μρ] Function.support V := by
      filter_upwards [hposρ] with x hx
      intro _
      change V x ≠ 0
      exact (ENNReal.ofReal_pos.mpr hx).ne'
    have hvolpos : 0 < μρ Set.univ := by
      have hcube := volume_originCube_pos (d := d) (by linarith : 0 < ρ)
      simpa [μρ] using hcube
    have hsupportpos : 0 < μρ (Function.support V) :=
      lt_of_lt_of_le hvolpos (measure_mono_ae hsupport)
    have hlintegralpos : 0 < ∫⁻ x, V x ∂μρ :=
      (lintegral_pos_iff_support hVmeas).2 hsupportpos
    have hreal : ENNReal.ofReal (bombieriMass v ρ) = ∫⁻ x, V x ∂μρ := by
      simpa [μρ, V, bombieriMass] using ofReal_integral_eq_lintegral_ofReal hIntρ hnonnegρ
    rw [← hreal] at hlintegralpos
    exact (ENNReal.ofReal_pos).mp hlintegralpos
  let f : ℝ → ℝ := bombieriEnvelope v
  have hmonotone : ∀ ρ R, 3 / 4 ≤ ρ → ρ ≤ R → R ≤ 7 / 8 → f ρ ≤ f R := by
    intro ρ R hρ hρR hR
    let μρ : Measure (Vec d) := volume.restrict (CoarseDeGiorgi.originCube ρ)
    let μR : Measure (Vec d) := volume.restrict (CoarseDeGiorgi.originCube R)
    have hsubset : CoarseDeGiorgi.originCube (d := d) ρ ⊆
        CoarseDeGiorgi.originCube (d := d) R := originCube_subset_of_le hρR
    have hμ : μρ ≤ μR := by
      dsimp [μρ, μR]
      exact Measure.restrict_mono hsubset le_rfl
    have hμR₀ : μR ≤ μ₀ := by
      dsimp [μR, μ₀]
      exact Measure.restrict_mono (originCube_subset_of_le hR) le_rfl
    have hIntR : Integrable v μR := hvint₀.mono_measure hμR₀
    have hnonnegR : ∀ᵐ x ∂μR, 0 ≤ v x := hnonneg₀.filter_mono (ae_mono hμR₀)
    have hI : bombieriMass v ρ ≤ bombieriMass v R := by
      exact integral_mono_measure hμ hnonnegR hIntR
    have hρpos := hIpositive ρ hρ (le_trans hρR hR)
    dsimp [f, bombieriEnvelope]
    exact max_le_max le_rfl (Real.log_le_log hρpos hI)
  have hstep : ∀ ρ R, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      f ρ ≤ f R / 2 + 3 * A₁ * (2 * A₂) ^ 6 * (R - ρ) ^ (-6 * ξ) := by
    intro ρ R hρ hρR hR
    let μρ : Measure (Vec d) := volume.restrict (CoarseDeGiorgi.originCube ρ)
    let μR : Measure (Vec d) := volume.restrict (CoarseDeGiorgi.originCube R)
    have hδpos : 0 < R - ρ := by linarith
    have hδle : R - ρ ≤ 1 := by linarith
    let x := 2 * A₂ * (R - ρ) ^ (-ξ)
    have hxtwo : 2 ≤ x := by
      dsimp [x]
      have hrpow := one_le_rpow_neg hδpos hδle hξ
      have hA₂ : 2 ≤ 2 * A₂ := by nlinarith [hA₂]
      calc
          2 ≤ 2 * A₂ := hA₂
          _ = (2 * A₂) * 1 := by ring
          _ ≤ (2 * A₂) * (R - ρ) ^ (-ξ) :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
    have hx : 1 ≤ x := le_trans (by norm_num : (1 : ℝ) ≤ 2) hxtwo
    have hxpow : 64 ≤ x ^ 6 := by
      calc
        64 = (2 : ℝ) ^ 6 := by norm_num
        _ ≤ x ^ 6 := by gcongr
    have hxpos : 0 < x := by linarith
    have hmassRpos := hIpositive R (le_trans hρ hρR.le) hR
    have hFnonneg : 0 ≤ f R := le_max_left _ _
    by_cases hsmall : f R < 3 * A₁ * x ^ 6
    · have hmono := hmonotone ρ R hρ hρR.le hR
      have hcost : 0 ≤ 3 * A₁ * x ^ 6 := by positivity
      have hstep' : f ρ ≤ f R / 2 + 3 * A₁ * x ^ 6 := by linarith
      have hδpower : ((R - ρ) ^ (-ξ)) ^ 6 = (R - ρ) ^ (-6 * ξ) := by
        rw [← Real.rpow_natCast ((R - ρ) ^ (-ξ)) 6]
        rw [← Real.rpow_mul (le_of_lt hδpos)]
        congr 1
        ring
      have hpower : x ^ 6 = (2 * A₂) ^ 6 * (R - ρ) ^ (-6 * ξ) := by
        dsimp [x]
        rw [mul_pow, hδpower]
      rw [hpower] at hstep'
      simpa [mul_assoc, mul_left_comm, mul_comm] using hstep'
    · have hlarge : 3 * A₁ * x ^ 6 ≤ f R := le_of_not_gt hsmall
      have hFpos : 0 < f R := by
        exact lt_of_lt_of_le (mul_pos (by positivity : 0 < 3 * A₁) (by positivity)) hlarge
      have hlogmassnonneg : 0 ≤ Real.log (bombieriMass v R) := by
        by_contra hneg
        have hneg' : Real.log (bombieriMass v R) < 0 := lt_of_not_ge hneg
        have hmax : max 0 (Real.log (bombieriMass v R)) = 0 :=
          max_eq_left (le_of_lt hneg')
        dsimp [f, bombieriEnvelope] at hFpos
        rw [hmax] at hFpos
        exact (lt_irrefl 0 hFpos)
      have hlogF : Real.log (bombieriMass v R) = f R := by
        dsimp [f, bombieriEnvelope]
        rw [max_eq_right hlogmassnonneg]
      have hA₁pos : 0 < A₁ := by linarith
      have hxpow_gt : 1 < x ^ 6 := by linarith [hxpow]
      have hA₁cost : 3 * A₁ < 3 * A₁ * x ^ 6 := by
        simpa using mul_lt_mul_of_pos_left hxpow_gt (by positivity : 0 < 3 * A₁)
      have hFlarge : 3 * A₁ < f R := lt_of_lt_of_le hA₁cost hlarge
      obtain ⟨b, hb, hb1, hbal⟩ := adaptive_exponent (f R) A₁ hA₁pos (by
        exact hFlarge)
      have hμR₀ : μR ≤ μ₀ := by
        dsimp [μR, μ₀]
        exact Measure.restrict_mono (originCube_subset_of_le hR) le_rfl
      have hIntR : Integrable v μR := hvint₀.mono_measure hμR₀
      have hposR : ∀ᵐ y ∂μR, 0 < v y := hpos.filter_mono (ae_mono hμR₀)
      have hnonnegR : ∀ᵐ y ∂μR, 0 ≤ v y := hposR.mono fun _ hy => hy.le
      have hVeq : ∫⁻ y, ENNReal.ofReal (v y) ∂μR =
          ENNReal.ofReal (bombieriMass v R) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hIntR hnonnegR
      have hV : ∫⁻ y, ENNReal.ofReal (v y) ∂μR ≤ ENNReal.ofReal (Real.exp (f R)) := by
        rw [hVeq, ← hlogF, Real.exp_log hmassRpos]
      have htail : μR {y | f R / 3 < Real.log (v y)} ≤
          ENNReal.ofReal (3 * A₁ / f R) := by
        exact log_tail_measure_bound_real hmeasSubtype (by linarith) hFlarge hR hlog
      have hmass : μR Set.univ ≤ 1 := by
        dsimp [μR]
        simpa using volume_originCube_le_one (d := d) (by linarith : R ≤ 1)
      have hsplit := log_power_integral_split hv hposR hA₁pos hFlarge hb hb1 hbal
        hmass hV htail
      have hsmallLp := eLpNorm_subunit_bound hv hposR hb hsplit
      have hIntρ : Integrable v μρ := hvint₀.mono_measure (by
        dsimp [μρ, μ₀]
        exact Measure.restrict_mono (originCube_subset_of_le (le_trans hρR.le hR)) le_rfl)
      have hnonnegρ : ∀ᵐ y ∂μρ, 0 ≤ v y :=
        hnonneg₀.filter_mono (ae_mono (by
          dsimp [μρ, μ₀]
          exact Measure.restrict_mono (originCube_subset_of_le (le_trans hρR.le hR)) le_rfl))
      have hIρpos := hIpositive ρ hρ (le_trans hρR.le hR)
      have hL1ρ := eLpNorm_one_eq_ofReal_integral hIntρ hnonnegρ
      have hL1ρ' : eLpNorm v 1 μρ = ENNReal.ofReal (bombieriMass v ρ) := by
        simpa [μρ, bombieriMass] using hL1ρ
      have hrev' := hrev b hb hb1 ρ R hρ hρR hR
      have hcoef_nonneg : 0 ≤ A₂ * (R - ρ) ^ (-ξ) := by positivity
      have hcoef_pow : (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) =
          ENNReal.ofReal ((A₂ * (R - ρ) ^ (-ξ)) ^ (1 / b)) :=
        ENNReal.ofReal_rpow_of_nonneg hcoef_nonneg (by positivity)
      have hsmallLp' : eLpNorm v (ENNReal.ofReal b) μR ≤
          ENNReal.ofReal (2 ^ (1 / b) * Real.exp (f R / 3)) := by
        simpa [μR] using hsmallLp
      have hprod : ENNReal.ofReal (bombieriMass v ρ) ≤
          ENNReal.ofReal ((A₂ * (R - ρ) ^ (-ξ)) ^ (1 / b)) *
            ENNReal.ofReal (2 ^ (1 / b) * Real.exp (f R / 3)) := by
        calc
          _ = eLpNorm v 1 μρ := hL1ρ'.symm
          _ ≤ ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ)) ^ (1 / b) *
              eLpNorm v (ENNReal.ofReal b) μR := by simpa [μρ, μR] using hrev'
          _ ≤ ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ)) ^ (1 / b) *
              ENNReal.ofReal (2 ^ (1 / b) * Real.exp (f R / 3)) := by
            exact mul_le_mul_of_nonneg_left hsmallLp' (by positivity)
          _ = _ := by rw [hcoef_pow]
      have hrealprod : bombieriMass v ρ ≤
          (A₂ * (R - ρ) ^ (-ξ)) ^ (1 / b) *
            (2 ^ (1 / b) * Real.exp (f R / 3)) := by
        have hprod' : ENNReal.ofReal (bombieriMass v ρ) ≤
            ENNReal.ofReal ((A₂ * (R - ρ) ^ (-ξ)) ^ (1 / b) *
              (2 ^ (1 / b) * Real.exp (f R / 3))) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          exact hprod
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hprod'
      have hlogIρ : Real.log (bombieriMass v ρ) ≤
          f R / 3 + (1 / b) * Real.log x := by
        have hlogmono := Real.log_le_log hIρpos hrealprod
        have hcoefpos : 0 < A₂ * (R - ρ) ^ (-ξ) := by positivity
        have hlogx : Real.log x = Real.log 2 +
            Real.log (A₂ * (R - ρ) ^ (-ξ)) := by
          calc
            Real.log x = Real.log (2 * (A₂ * (R - ρ) ^ (-ξ))) := by
              congr 1
              dsimp [x]
              ring
            _ = Real.log 2 + Real.log (A₂ * (R - ρ) ^ (-ξ)) :=
              Real.log_mul (by norm_num) (ne_of_gt hcoefpos)
        have hlogexp : Real.log (Real.exp (f R / 3)) = f R / 3 := Real.log_exp _
        have hlogs : Real.log ((A₂ * (R - ρ) ^ (-ξ)) ^ (1 / b) *
              (2 ^ (1 / b) * Real.exp (f R / 3))) =
              (1 / b) * Real.log x + f R / 3 := by
          rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hcoefpos _))
              (ne_of_gt (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.exp_pos _))),
            Real.log_rpow hcoefpos,
            Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
              (ne_of_gt (Real.exp_pos _)),
            Real.log_rpow (by norm_num : (0 : ℝ) < 2), hlogexp]
          rw [hlogx]
          ring
        rw [hlogs] at hlogmono
        linarith
      have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
      have hdenpos : 0 < Real.log (f R / (3 * A₁)) :=
        Real.log_pos ((one_lt_div (by positivity)).2 hFlarge)
      have hratio : Real.log x / Real.log (f R / (3 * A₁)) ≤ 1 / 6 := by
        have hloglarge : 6 * Real.log x ≤ Real.log (f R / (3 * A₁)) := by
          have hdiv : x ^ 6 ≤ f R / (3 * A₁) := by
            apply (le_div_iff₀ (by positivity : 0 < 3 * A₁)).2
            calc
              x ^ 6 * (3 * A₁) = 3 * A₁ * x ^ 6 := by ring
              _ ≤ f R := hlarge
          have hlogpow : Real.log (x ^ 6) ≤ Real.log (f R / (3 * A₁)) :=
            Real.log_le_log (by positivity) hdiv
          rw [Real.log_pow] at hlogpow
          exact hlogpow
        have hratio' : Real.log x ≤ (1 / 6 : ℝ) * Real.log (f R / (3 * A₁)) := by
          calc
            Real.log x = (1 / 6 : ℝ) * (6 * Real.log x) := by ring
            _ ≤ (1 / 6 : ℝ) * Real.log (f R / (3 * A₁)) := by
              exact mul_le_mul_of_nonneg_left hloglarge (by norm_num)
        exact (div_le_iff₀ hdenpos).2 hratio'
      have hbal' := adaptive_exponent_inverse hA₁pos hFlarge hb hbal
      have hthresholdarith := bombieri_large_threshold_arithmetic
        hA₁ hFnonneg hdenpos (log_le_sixth_power hx) hratio hbal'
      have hconverted : f ρ ≤ f R / 2 + 3 * A₁ * x ^ 6 := by
        have hlognonneg : 0 ≤ f R / 3 + (1 / b) * Real.log x := by positivity
        have hmax : max 0 (Real.log (bombieriMass v ρ)) ≤
            f R / 3 + (1 / b) * Real.log x := by
          apply max_le
          · exact hlognonneg
          · exact hlogIρ
        calc
          f ρ ≤ max 0 (Real.log (bombieriMass v ρ)) := by rfl
          _ ≤ f R / 3 + (1 / b) * Real.log x := hmax
          _ ≤ f R / 2 + 3 * A₁ * x ^ 6 := hthresholdarith
      have hpower : x ^ 6 = (2 * A₂) ^ 6 * (R - ρ) ^ (-6 * ξ) := by
        simpa [x] using bombieri_scale_power_six (A := A₂) (δ := R - ρ)
          (ξ := ξ) (le_of_lt hδpos)
      rw [hpower] at hconverted
      simpa [mul_assoc, mul_left_comm, mul_comm] using hconverted
  let K := 3 * A₁ * (2 * A₂) ^ 6
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound : ∀ r, 3 / 4 ≤ r → r ≤ 7 / 8 → f r ≤ f (7 / 8) := by
    intro r hr hrtop
    exact hmonotone r (7 / 8) hr hrtop (by norm_num)
  have hiter := bombieri_radius_iteration hξ hK hbound (by
    intro ρ R hρ hρR hR
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hstep ρ R hρ hρR hR)
  have hfinalf : f (3 / 4) ≤ C * A₁ * A₂ ^ 6 := by
    calc
      f (3 / 4) ≤ K * (8 / (1 - bombieriRadiusRatio ξ)) ^ (6 * ξ) *
          (1 - bombieriSeriesRatio)⁻¹ := hiter
      _ = C * A₁ * A₂ ^ 6 := by dsimp [K, C]; ring
  have hIinitial : bombieriMass v (3 / 4) ≤ Real.exp (f (3 / 4)) := by
    have hIp := hIpositive (3 / 4) (by norm_num) (by norm_num)
    dsimp [f, bombieriEnvelope]
    have hle : Real.log (bombieriMass v (3 / 4)) ≤
        max 0 (Real.log (bombieriMass v (3 / 4))) := le_max_right _ _
    have hlog := Real.exp_le_exp.mpr hle
    simpa [Real.exp_log hIp] using hlog
  have hrealfinal : bombieriMass v (3 / 4) ≤ Real.exp (C * A₁ * A₂ ^ 6) := by
    have hexp := Real.exp_le_exp.mpr hfinalf
    exact hIinitial.trans hexp
  have hIntinitial : Integrable v
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) (3 / 4))) :=
    hvint₀.mono_measure (by
      dsimp [μ₀]
      exact Measure.restrict_mono (originCube_subset_of_le (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)) le_rfl)
  have hnonneginitial : ∀ᵐ y ∂volume.restrict (CoarseDeGiorgi.originCube (d := d) (3 / 4)),
      0 ≤ v y := hnonneg₀.filter_mono (ae_mono (by
        dsimp [μ₀]
        exact Measure.restrict_mono (originCube_subset_of_le (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)) le_rfl))
  rw [eLpNorm_one_eq_ofReal_integral hIntinitial hnonneginitial]
  exact ENNReal.ofReal_le_ofReal hrealfinal
