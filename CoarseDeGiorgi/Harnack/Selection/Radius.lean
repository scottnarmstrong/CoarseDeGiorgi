import CoarseDeGiorgi.Adapters.UniformSurface
import CoarseDeGiorgi.Harnack.Selection.CoareaLr
import CoarseDeGiorgi.Selection.QuantitativeRadius
import CoarseDeGiorgi.Selection.SourceRadius
import CoarseDeGiorgi.Selection.SurfaceEnergy

namespace CoarseDeGiorgi.Harnack.Selection

open Homogenization MeasureTheory Set CoarseDeGiorgi.Selection
open scoped ENNReal BigOperators

noncomputable section

/-- Uniform four-slot surface selection: response, fractional trace, Lr trace, and optional L2
trace share one radius with the centered surface-energy maximal bound. The trace/subsequence
property `Good` is retained at the selected radius. -/
theorem exists_uniform_four_slot_surface_constant {n : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ T : ℝ, 0 < T ∧ ∀ ρ R p : ℝ,
      (1 / 2 : ℝ) ≤ ρ → R ≤ 1 → ρ < R → 1 ≤ p →
      ∀ (F w v : Vec (n + 1) → ℝ) (L E Bresponse : ℝ≥0∞)
        (g : Vec (n + 1) → ℝ≥0∞) (S : ℝ → ℝ≥0∞) (Good : ℝ → Prop),
        Measurable F → Measurable w → Measurable v → Measurable g → Measurable S →
        (∀ᵐ τ ∂volume.restrict (selectionInterval ρ R),
          F =ᵐ[CoarseDeGiorgi.surfaceMeasure τ] w) →
        fracNorm univ α r F ≤ L → E ≠ ⊤ →
        (∫⁻ x in cubicalAnnulus (n + 1) ρ R, g x) ≤ E →
        powerNorm (2 * p) volume S ≤ Bresponse →
        (∀ᵐ τ ∂volume.restrict (selectionInterval ρ R), Good τ) →
        ∃ τ ∈ selectionInterval ρ R, Good τ ∧
          S τ ≤ ENNReal.ofReal (32 / (R - ρ)) ^ (1 / (2 * p)) * Bresponse ∧
          surfaceFracNorm τ α r w ≤
            ENNReal.ofReal (32 / (R - ρ)) ^ (1 / r) * ENNReal.ofReal T ^ (1 / r) * L ∧
          eLpNorm v (ENNReal.ofReal r) (CoarseDeGiorgi.surfaceMeasure τ) ≤
            ENNReal.ofReal (32 / (R - ρ)) ^ (1 / r) * (2 : ℝ≥0∞) ^ (1 / r) *
              eLpNorm v (ENNReal.ofReal r) (volume.restrict (originCube R)) ∧
          eLpNorm v 2 (CoarseDeGiorgi.surfaceMeasure τ) ≤
            ENNReal.ofReal (32 / (R - ρ)) ^ (1 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
              eLpNorm v 2 (volume.restrict (originCube R)) ∧
          surfaceEnergyMaximal ρ R g τ ≤ 192 * (ENNReal.ofReal (R - ρ))⁻¹ * E := by
  obtain ⟨T, hT, htrace⟩ := Adapters.exists_uniform_trace_constant (n := n) hα0 hα1 hr
  refine ⟨T, hT, ?_⟩
  intro ρ R p hρ hR hgap hp F w v L E Bresponse g S Good hF hw hv hg hS hagree hL hEtop hE hresponse hgood
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hp0 : 0 < 2 * p := by linarith only [hp]
  have hρ0 : 0 ≤ ρ := by linarith only [hρ]
  have hδ : 0 < R - ρ := sub_pos.mpr hgap
  have hEannTop : (∫⁻ x in cubicalAnnulus (n + 1) ρ R, g x) ≠ ⊤ :=
    ne_top_of_le_ne_top hEtop hE
  let ν := surfaceEnergyMeasure ρ R g
  have hνfinite : IsFiniteMeasure ν := surfaceEnergyMeasure_finite hρ0 hg hEannTop
  have hmass : ν univ ≤ 2 * E := by
    rw [surfaceEnergyMeasure_univ hρ0 hg]
    exact mul_le_mul_right hE 2
  let K : ℝ≥0∞ := ENNReal.ofReal (32 / (R - ρ))
  have hK0 : K ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinv : K⁻¹ = ENNReal.ofReal ((R - ρ) / 32) := by
    rw [show K = ENNReal.ofReal (32 / (R - ρ)) by rfl,
      ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 32 / (R - ρ))]
    congr 1
    field_simp
  have hsmall : ((Fintype.card (Fin 4) + 1 : ℕ) : ℝ≥0∞) * K⁻¹ <
      volume (selectionInterval ρ R) := by
    rw [hinv, volume_selectionInterval]
    norm_num only [Fintype.card_fin, Nat.reduceAdd]
    rw [← ENNReal.ofReal_ofNat (n := 5)]
    change ENNReal.ofReal 5 * ENNReal.ofReal ((R - ρ) / 32) <
      ENNReal.ofReal ((R - ρ) / 4)
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  let f : Fin 4 → ℝ → ℝ≥0∞ := ![
    S,
    (fun τ => surfaceFracNorm τ α r w),
    (fun τ => eLpNorm v (ENNReal.ofReal r) (CoarseDeGiorgi.surfaceMeasure τ)),
    (fun τ => eLpNorm v 2 (CoarseDeGiorgi.surfaceMeasure τ))]
  let exponent : Fin 4 → ℝ := ![2 * p, r, r, 2]
  let B : Fin 4 → ℝ≥0∞ := ![
    Bresponse,
    ENNReal.ofReal T ^ (1 / r) * L,
    (2 : ℝ≥0∞) ^ (1 / r) *
      eLpNorm v (ENNReal.ofReal r) (volume.restrict (originCube R)),
    (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm v 2 (volume.restrict (originCube R))]
  have hf (i : Fin 4) : Measurable (f i) := by
    fin_cases i
    · exact hS
    · exact measurable_surfaceFracNorm hw α hr0
    · exact measurable_surface_eLpNorm hv hr0
    · change Measurable (fun τ => eLpNorm v 2 (CoarseDeGiorgi.surfaceMeasure τ))
      simpa only [ENNReal.ofReal_ofNat] using
        measurable_surface_eLpNorm hv (by norm_num : (0 : ℝ) < 2)
  have hexp (i : Fin 4) : 0 < exponent i := by
    fin_cases i
    · exact hp0
    · exact hr0
    · exact hr0
    · norm_num [exponent]
  have hint (i : Fin 4) :
      ∫⁻ τ in selectionInterval ρ R, (f i τ) ^ exponent i ≤ B i ^ exponent i := by
    fin_cases i
    · calc
        ∫⁻ τ in selectionInterval ρ R, S τ ^ (2 * p) ≤ ∫⁻ τ, S τ ^ (2 * p) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
        _ = powerNorm (2 * p) volume S ^ (2 * p) :=
          (powerNorm_rpow hp0 volume S).symm
        _ ≤ Bresponse ^ (2 * p) :=
          ENNReal.rpow_le_rpow hresponse (by linarith only [hp])
    · have hfr := htrace ρ R hρ hR hgap F w L hF hagree hL
      have hn : powerNorm r (volume.restrict (selectionInterval ρ R))
          (fun τ => surfaceFracNorm τ α r w) ≤ ENNReal.ofReal T ^ (1 / r) * L := by
        apply (ENNReal.rpow_le_rpow hfr (one_div_nonneg.mpr hr0.le)).trans_eq
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le),
          ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
      calc
        _ = powerNorm r (volume.restrict (selectionInterval ρ R))
            (fun τ => surfaceFracNorm τ α r w) ^ r :=
          (powerNorm_rpow hr0 (volume.restrict (selectionInterval ρ R)) _).symm
        _ ≤ (ENNReal.ofReal T ^ (1 / r) * L) ^ r :=
          ENNReal.rpow_le_rpow hn hr0.le
        _ = B 1 ^ exponent 1 := by rfl
    · have hcoarea := surface_Lr_integral_le hρ0 hgap hr0 hv
      have hBpow : ((2 : ℝ≥0∞) ^ (1 / r) *
          eLpNorm v (ENNReal.ofReal r) (volume.restrict (originCube R))) ^ r =
          2 * eLpNorm v (ENNReal.ofReal r) (volume.restrict (originCube R)) ^ r := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul,
          one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
      simpa [f, exponent, B, ENNReal.ofReal_ofNat] using hcoarea.trans_eq hBpow.symm
    · have hcoarea := surface_Lr_integral_le hρ0 hgap
        (by norm_num : (0 : ℝ) < 2) hv
      have hcoarea' :
          (∫⁻ τ in selectionInterval ρ R,
            eLpNorm v 2 (CoarseDeGiorgi.surfaceMeasure τ) ^ (2 : ℝ)) ≤
          2 * eLpNorm v 2 (volume.restrict (originCube R)) ^ (2 : ℝ) := by
        simpa only [ENNReal.ofReal_ofNat] using hcoarea
      have hBpow : ((2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          eLpNorm v 2 (volume.restrict (originCube R))) ^ (2 : ℝ) =
          2 * eLpNorm v 2 (volume.restrict (originCube R)) ^ (2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
      simpa [f, exponent, B] using hcoarea'.trans_eq hBpow.symm
  obtain ⟨τ, hτ, hGoodτ, hb, hmax⟩ := one_radius_of_integral_bounds ν
    hK0 hKtop hEtop hmass f exponent B hf hexp hint hgood hsmall
  have hmaxFactor : 6 * K = 192 * (ENNReal.ofReal (R - ρ))⁻¹ := by
    dsimp [K]
    rw [ENNReal.ofReal_div_of_pos hδ]
    rw [div_eq_mul_inv]
    norm_num
    ring
  have hmax' : surfaceEnergyMaximal ρ R g τ ≤
      192 * (ENNReal.ofReal (R - ρ))⁻¹ * E := by
    change centeredMaximal ν τ ≤ _
    calc
      _ ≤ 6 * K * E := hmax
      _ = 192 * (ENNReal.ofReal (R - ρ))⁻¹ * E := by rw [hmaxFactor]
  refine ⟨τ, hτ, hGoodτ, ?_, ?_, ?_, ?_, hmax'⟩
  · simpa [f, exponent, B, K] using hb 0
  · simpa [f, exponent, B, K, mul_assoc] using hb 1
  · simpa [f, exponent, B, K, mul_assoc] using hb 2
  · simpa [f, exponent, B, K, mul_assoc] using hb 3

end
end CoarseDeGiorgi.Harnack.Selection
