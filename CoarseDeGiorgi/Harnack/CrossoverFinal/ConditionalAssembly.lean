import CoarseDeGiorgi.Harnack.CrossoverFinal.BombieriBridge
import CoarseDeGiorgi.Harnack.CrossoverFinal.CenteredLogNorm
import CoarseDeGiorgi.Harnack.CrossoverFinal.EnnrealAverage
import CoarseDeGiorgi.Harnack.CrossoverFinal.LogCenter
import CoarseDeGiorgi.Harnack.CrossoverFinal.Parameters
import CoarseDeGiorgi.Harnack.CrossoverFinal.PowerIntegrability
import CoarseDeGiorgi.Harnack.Crossover.FinalScalarCancellation
import CoarseDeGiorgi.Harnack.Crossover.ScalarPremises
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.CrossoverExponent
import CoarseDeGiorgi.Statements.ChiParam
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta

namespace CoarseDeGiorgi.Harnack.CrossoverFinal

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- Assemble the crossover estimate `l.crossover` from the log-estimate input
and the two all-radii iteration families supplied as inputs. -/
theorem crossover_of_iterations_and_log_estimate_input
    (hLog : logEstimateInputContract)
    (hIterations : ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C₃ γ₆ : ℝ, 1 ≤ C₃ ∧ 0 < γ₆ ∧
        ∀ c : ℝ, 0 < c →
        c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) →
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube (d := d) 1) a)
          (_hrange : spatialMomentRange a ha p q s t)
          (u : Vec d → ℝ) (G : Vec d → Vec d)
          (_hu : IsWeightedSupersolution a (originCube (d := d) 1) u G)
          (_hnonneg : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), 0 ≤ u x)
          (ε : ℝ) (_hε : 0 < ε),
        let pC : ℝ := crossoverExponent c a ha s t p q hs ht
          (le_of_lt hp) (le_of_lt hq)
        (∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
          eLpNorm (fun x => (u x + ε) ^ pC) 1
              (volume.restrict (originCube ρ)) ≤
            (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
              eLpNorm (fun x => (u x + ε) ^ pC)
                (ENNReal.ofReal b) (volume.restrict (originCube R))) ∧
        (∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
          eLpNorm (fun x => (u x + ε) ^ (-pC)) 1
              (volume.restrict (originCube ρ)) ≤
            (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
              eLpNorm (fun x => (u x + ε) ^ (-pC))
                (ENNReal.ofReal b) (volume.restrict (originCube R)))) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ c : ℝ, 0 < c ∧
        c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) ∧
        ∃ C : ℝ≥0∞, C < ⊤ ∧
          ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube (d := d) 1) a),
            spatialMomentRange a ha p q s t →
            ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
              (∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), 0 ≤ u x) →
              IsWeightedSupersolution a (originCube (d := d) 1) u G →
              ∀ ε : ℝ, 0 < ε →
                let b := crossoverExponent c a ha s t p q hs ht
                  (le_of_lt hp) (le_of_lt hq)
                ((volume (originCube (d := d) (3 / 4)))⁻¹ *
                  ∫⁻ x in originCube (d := d) (3 / 4),
                    ENNReal.ofReal ((u x + ε) ^ b)) *
                ((volume (originCube (d := d) (3 / 4)))⁻¹ *
                  ∫⁻ x in originCube (d := d) (3 / 4),
                    ENNReal.ofReal ((u x + ε) ^ (-b))) ≤ C := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C₂, hC₂, hcenterAll⟩ :=
    crossover_log_center_bound_of_log_estimate hLog hd p q s t hp hq hs ht hθ
  obtain ⟨C₃, γ₆, hC₃, hγ₆, hIterationAll⟩ :=
    hIterations d hd p q s t hp hq hs ht hθ
  obtain ⟨c, hc, hcRange, hcc⟩ :=
    exists_crossover_parameter hd p q s t C₂ hp hq hs ht hθ hC₂
  obtain ⟨Cξ, hCξ, hBombieri⟩ :=
    bombieri_integral_bound_of_integrable_log_eLpNorm hγ₆
  let A₂ : ℝ := (2 : ℝ) ^ d * C₃
  have hA₂ : 1 ≤ A₂ := by
    dsimp [A₂]
    have hd2 : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    calc
      1 ≤ (2 : ℝ) ^ d := hd2
      _ ≤ (2 : ℝ) ^ d * C₃ := by
        simpa using (mul_le_mul_of_nonneg_left hC₃ (le_trans (by norm_num) hd2))
  let V₃ := originCube (d := d) (3 / 4 : ℝ)
  let V₇ := originCube (d := d) (7 / 8 : ℝ)
  have hV₃finite : volume V₃ < ⊤ := by
    exact lt_of_le_of_lt
      (Harnack.Scalar.volume_originCube_le_one (d := d) (by norm_num))
      ENNReal.one_lt_top
  have hV₃pos : 0 < volume V₃ :=
    Harnack.Scalar.volume_originCube_pos (d := d) (by norm_num)
  let K : ℝ := Real.exp (Cξ * A₂ ^ 6)
  let C₀ : ℝ := ((volume V₃).toReal⁻¹ * K) ^ 2
  let C : ℝ≥0∞ := ENNReal.ofReal C₀
  have hC₀ : 0 ≤ C₀ := sq_nonneg _
  have hCfinite : C < ⊤ := by simp [C]
  refine ⟨c, hc, hcRange, C, hCfinite, ?_⟩
  intro a ha hrange u G hnonneg hu ε hε
  let pC := crossoverExponent c a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)
  let U : Vec d → ℝ := fun x => u x + ε
  let wplus := Harnack.Crossover.centeredWeight V₇ U pC
  let wminus := Harnack.Crossover.centeredWeightInv V₇ U pC
  have hcenter := hcenterAll a ha hrange u G hnonneg hu ε hε
  obtain ⟨hplusInt, hminusInt⟩ :=
    shifted_signed_powers_integrable_of_supersolution hd p q s t hp hq hs ht
      hθ a ha hrange c hc hcRange u G hnonneg hu ε hε
  have hlogNorm := centered_weight_log_eLpNorm_le_one_of_log_estimate hLog
      hd p q s t hp hq hs ht hθ C₂ hC₂ a ha hrange u G hnonneg hu ε hε
      c hc hcc hcenter
  obtain ⟨hplus, hminus⟩ :=
    hIterationAll c hc hcRange a ha hrange u G hu hnonneg ε hε
  have hV₇subset : V₇ ⊆ originCube (d := d) 1 :=
    Harnack.Scalar.originCube_subset_of_le_one (by norm_num)
  have hμ₇ : volume.restrict V₇ ≤
      volume.restrict (originCube (d := d) 1) :=
    Measure.restrict_mono hV₇subset le_rfl
  have hnonneg₇ := ae_mono hμ₇ hnonneg
  have hUpos : ∀ᵐ x ∂(volume.restrict V₇), 0 < U x := by
    filter_upwards [hnonneg₇] with x hx
    dsimp [U]
    linarith
  have hweightInt :=
    Harnack.Crossover.centered_weights_integrable_of_shifted_powers
      V₇ U pC hplusInt hminusInt
  have hweightPos := Harnack.Crossover.centered_weights_positive_ae V₇ U pC hUpos
  have hweightReverse := Harnack.Crossover.crossover_reverse_moments_of_iterations
    U pC A₂ γ₆ hA₂ hplus hminus
  have hreversePlus : ∀ b : ℝ, 0 < b → b < 1 →
      ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
        eLpNorm wplus 1 (volume.restrict (originCube ρ)) ≤
          (ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
            eLpNorm wplus (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
    intro b hb hb1 ρ R hρ hρR hR
    exact hweightReverse.1 hb hb1 hρ hρR hR
  have hreverseMinus : ∀ b : ℝ, 0 < b → b < 1 →
      ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
        eLpNorm wminus 1 (volume.restrict (originCube ρ)) ≤
          (ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
            eLpNorm wminus (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
    intro b hb hb1 ρ R hρ hρR hR
    exact hweightReverse.2 hb hb1 hρ hρR hR
  have hscalarPlus := hBombieri d A₂ hA₂ wplus hweightPos.1 hweightInt.1
    hlogNorm.1 hreversePlus
  have hscalarMinus := hBombieri d A₂ hA₂ wminus hweightPos.2 hweightInt.2
    hlogNorm.2 hreverseMinus
  have hUposSmall : ∀ᵐ x ∂(volume.restrict V₃), 0 < U x := by
    have hμ₃ : volume.restrict V₃ ≤ volume.restrict V₇ := by
      apply Measure.restrict_mono
      · exact Harnack.Scalar.originCube_subset_of_le (by norm_num)
      · exact le_rfl
    exact ae_mono hμ₃ hUpos
  have hplusNonneg : 0 ≤ᵐ[volume.restrict V₃] (fun x => U x ^ pC) := by
    filter_upwards [hUposSmall] with x hx
    exact (Real.rpow_pos_of_pos hx pC).le
  have hminusNonneg : 0 ≤ᵐ[volume.restrict V₃] (fun x => U x ^ (-pC)) := by
    filter_upwards [hUposSmall] with x hx
    exact (Real.rpow_pos_of_pos hx (-pC)).le
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hproductReal := Harnack.Crossover.crossover_product_bound_of_centered_integral_bounds
    U pC K hK hUpos hplusInt hminusInt
    (by simpa [wplus, Harnack.Crossover.centeredWeight, V₇, U] using hscalarPlus.1)
    (by simpa [wplus, Harnack.Crossover.centeredWeight, V₇, U] using hscalarPlus.2)
    (by simpa [wminus, Harnack.Crossover.centeredWeightInv, V₇, U] using hscalarMinus.1)
    (by simpa [wminus, Harnack.Crossover.centeredWeightInv, V₇, U] using hscalarMinus.2)
  have hplusInt₃ : IntegrableOn (fun x => U x ^ pC) V₃ :=
    hplusInt.mono_set (Harnack.Scalar.originCube_subset_of_le (by norm_num))
  have hminusInt₃ : IntegrableOn (fun x => U x ^ (-pC)) V₃ :=
    hminusInt.mono_set (Harnack.Scalar.originCube_subset_of_le (by norm_num))
  have hproductENN := ennrealAverage_product_le_of_volumeAverage_product
    V₃ hV₃finite hV₃pos (fun x => U x ^ pC) (fun x => U x ^ (-pC))
    hplusInt₃ hminusInt₃ hplusNonneg hminusNonneg C₀ hC₀
    (by simpa [C₀, K, V₃] using hproductReal)
  simpa [C, C₀, U, pC, V₃] using hproductENN

end

end CoarseDeGiorgi.Harnack.CrossoverFinal
