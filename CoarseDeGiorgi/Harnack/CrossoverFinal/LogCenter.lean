import CoarseDeGiorgi.Harnack.Crossover.Normalization
import CoarseDeGiorgi.Harnack.Log.Centering
import CoarseDeGiorgi.Harnack.LogLimit.OverlapHolder
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.WeightedEnergy

namespace CoarseDeGiorgi.Harnack.CrossoverFinal

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The statement of `log_estimate` (`l.log.estimate`), repeated as the explicit input
consumed below. -/
abbrev logEstimateInputContract : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
    (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
    0 < paramTheta d p q s t →
    ∃ C_E C₂ : ℝ≥0∞, C_E < ⊤ ∧ C₂ < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε →
            MemH1a a (originCube 1) (fun x => Real.log (u x + ε))
                (fun x => (u x + ε)⁻¹ • G x) ∧
              weightedEnergy a (originCube (15 / 16))
                  (fun x => (u x + ε)⁻¹ • G x) ≤
                C_E * upperMoment a ha s p hs (le_of_lt hp) ∧
              IntegrableOn (fun x => Real.log (u x + ε)) (originCube (7 / 8)) ∧
              eLpNorm (fun x => Real.log (u x + ε) -
                  volumeAverage (originCube (7 / 8)) (fun y => Real.log (u y + ε)))
                (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube (7 / 8))) ≤
                C₂ * (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                  (1 / 2)

/-- The `log_estimate` input supplies the centered L¹ log bound needed to
normalize both powers. The output constant depends only on the fixed
parameters; no coefficient, solution, or shift enters its choice. -/
theorem crossover_log_center_bound_of_log_estimate
    (hLog : logEstimateInputContract) {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε →
            volumeAverage (originCube (d := d) (7 / 8 : ℝ))
              (fun x => |Real.log (u x + ε) -
                volumeAverage (originCube (7 / 8 : ℝ))
                  (fun y => Real.log (u y + ε))|) ≤
              C₂ * Real.sqrt
                (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).toReal := by
  obtain ⟨C_E, C₂E, hCE, hC₂E, hLogAll⟩ := hLog d hd p q s t hp hq hs ht hθ
  let V := originCube (d := d) (7 / 8 : ℝ)
  let r := paramR q
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hVpos, hVfinite⟩ := Harnack.Log.originCube_sevenEighths_volume_facts (d := d)
  let : IsFiniteMeasure (volume.restrict V) := by
    simpa [V] using hVfinite
  have hVtop : volume V < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hmassTop : (volume.restrict V) Set.univ = ⊤ := by
      rw [Measure.restrict_apply_univ, htop]
    exact (measure_ne_top (volume.restrict V) Set.univ) hmassTop
  have hr : 1 < r := by
    dsimp [r, paramR]
    rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  have hmassPos : 0 < (volume V).toReal :=
    ENNReal.toReal_pos hVpos.ne' hVtop.ne
  let H : ℝ := (volume V).toReal ^ (1 - 1 / r) * (volume V).toReal⁻¹
  let C₂ : ℝ := C₂E.toReal * H
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hC₂nonneg : 0 ≤ C₂ := by
    dsimp [C₂]
    exact mul_nonneg ENNReal.toReal_nonneg hHnonneg
  refine ⟨C₂, hC₂nonneg, ?_⟩
  intro a ha hrange u G hnonneg hu ε hε
  let θ : ℝ≥0∞ := contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)
  have hθtop : θ < ⊤ := by
    dsimp [θ]
    exact Harnack.Crossover.contrast_lt_top_of_spatialMomentRange
      a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq) hrange
  obtain ⟨_, _, _, hLogOsc⟩ := hLogAll a ha hrange u G hnonneg hu ε hε
  have hθpowTop : θ.rpow (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hθtop.ne
  have hprodTop : C₂E * θ.rpow (1 / 2 : ℝ) ≠ ⊤ :=
    (ENNReal.mul_ne_top hC₂E.ne hθpowTop)
  have hrealRpow : θ.toReal ^ (1 / 2 : ℝ) =
      (θ.rpow (1 / 2 : ℝ)).toReal := ENNReal.toReal_rpow θ (1 / 2)
  have hrealProd : (C₂E * θ.rpow (1 / 2 : ℝ)).toReal =
      C₂E.toReal * Real.sqrt θ.toReal := by
    calc
      (C₂E * θ.rpow (1 / 2 : ℝ)).toReal =
          C₂E.toReal * (θ.rpow (1 / 2 : ℝ)).toReal := ENNReal.toReal_mul
      _ = C₂E.toReal * θ.toReal ^ (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ => C₂E.toReal * x) hrealRpow.symm
      _ = C₂E.toReal * Real.sqrt θ.toReal := by rw [Real.sqrt_eq_rpow]
  have hLp : eLpNorm
      (fun x => Real.log (u x + ε) - volumeAverage V (fun y => Real.log (u y + ε)))
      (ENNReal.ofReal r) (volume.restrict V) ≤
        ENNReal.ofReal (C₂E.toReal * Real.sqrt θ.toReal) := by
    have hEq : ENNReal.ofReal (C₂E.toReal * Real.sqrt θ.toReal) =
        C₂E * θ.rpow (1 / 2 : ℝ) := by
      rw [← hrealProd, ENNReal.ofReal_toReal hprodTop]
    rw [hEq]
    exact hLogOsc
  have hBnonneg : 0 ≤ C₂E.toReal * Real.sqrt θ.toReal := by positivity
  have hL1 := Harnack.LogLimit.integral_abs_le_of_eLpNorm_le
    (f := fun x => Real.log (u x + ε) - volumeAverage V
      (fun y => Real.log (u y + ε))) hr hBnonneg hLp
  have hIntegral : ∫ x in V,
      |Real.log (u x + ε) - volumeAverage V (fun y => Real.log (u y + ε))| ≤
        (C₂E.toReal * Real.sqrt θ.toReal) * (volume V).toReal ^ (1 - 1 / r) := by
    simpa [V, r, Real.norm_eq_abs] using hL1.2
  change (volume V).toReal⁻¹ *
      ∫ x in V,
        |Real.log (u x + ε) - volumeAverage V (fun y => Real.log (u y + ε))| ≤
    C₂ * Real.sqrt θ.toReal
  calc
    _ ≤ (volume V).toReal⁻¹ *
          ((C₂E.toReal * Real.sqrt θ.toReal) *
            (volume V).toReal ^ (1 - 1 / r)) :=
      mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr hmassPos.le)
    _ = C₂ * Real.sqrt θ.toReal := by
      dsimp [C₂, H]
      ring

end

end CoarseDeGiorgi.Harnack.CrossoverFinal
