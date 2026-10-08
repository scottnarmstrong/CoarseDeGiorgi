module

public import CoarseDeGiorgi.Statements.BombieriIntegralBound
public import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas
public import CoarseDeGiorgi.Harnack.Scalar.BombieriCore
public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

namespace CoarseDeGiorgi.Harnack.CrossoverFinal

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The scalar Bombieri lemma `bombieri_integral_bound` (`l.bombieri`) in the Bochner
integral form needed in the crossover argument, with the logarithm input supplied as an
L¹ norm. -/
theorem bombieri_integral_bound_of_log_eLpNorm {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ Cξ : ℝ, 0 < Cξ ∧
      ∀ (d : ℕ) (A₂ : ℝ), 1 ≤ A₂ →
        ∀ v : Vec d → ℝ,
          Measurable
            (fun x : originCube (d := d) (7 / 8) => v x) →
          (∀ᵐ x ∂(volume.restrict (originCube (d := d) (7 / 8))), 0 < v x) →
          IntegrableOn v (originCube (d := d) (7 / 8)) →
          eLpNorm (fun x => Real.log (v x)) 1
            (volume.restrict (originCube (d := d) (7 / 8))) ≤ 1 →
          (∀ b : ℝ, 0 < b → b < 1 →
            ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
              eLpNorm v 1 (volume.restrict (originCube ρ)) ≤
                (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) *
                  eLpNorm v (ENNReal.ofReal b) (volume.restrict (originCube R))) →
          (0 ≤ ∫ x in originCube (d := d) (3 / 4), v x ∧
            (∫ x in originCube (d := d) (3 / 4), v x) ≤
              Real.exp (Cξ * A₂ ^ 6)) := by
  obtain ⟨Cξ, hCξ, hscalar⟩ := CoarseDeGiorgi.bombieri_integral_bound ξ hξ
  refine ⟨Cξ, hCξ, ?_⟩
  intro d A₂ hA₂ v hv hpos hint hlog hrev
  have hlog' : eLpNorm (fun x => Real.log (v x)) 1
      (volume.restrict (originCube (d := d) (7 / 8))) ≤ ENNReal.ofReal 1 := by
    simpa using hlog
  have hbound := hscalar d 1 A₂ (by norm_num) hA₂ v hv hpos hint hlog' hrev
  have hsubset : originCube (d := d) (3 / 4) ⊆
      originCube (d := d) (7 / 8) :=
    Harnack.Scalar.originCube_subset_of_le (by norm_num)
  have hμ : volume.restrict (originCube (d := d) (3 / 4)) ≤
      volume.restrict (originCube (d := d) (7 / 8)) :=
    Measure.restrict_mono hsubset le_rfl
  have hintSmall : Integrable v
      (volume.restrict (originCube (d := d) (3 / 4))) := by
    change Integrable v (volume.restrict (originCube (d := d) (7 / 8))) at hint
    exact hint.mono_measure hμ
  have hposSmall : ∀ᵐ x ∂(volume.restrict (originCube (d := d) (3 / 4))),
      0 ≤ v x := by
    have hposSmall' := hpos.filter_mono (ae_mono hμ)
    filter_upwards [hposSmall'] with x hx
    exact hx.le
  have hnorm : eLpNorm v 1
      (volume.restrict (originCube (d := d) (3 / 4))) =
        ENNReal.ofReal (∫ x in originCube (d := d) (3 / 4), v x) := by
    exact Harnack.Scalar.eLpNorm_one_eq_ofReal_integral hintSmall hposSmall
  have hbound' : ENNReal.ofReal
      (∫ x in originCube (d := d) (3 / 4), v x) ≤
        ENNReal.ofReal (Real.exp (Cξ * A₂ ^ 6)) := by
    rw [← hnorm]
    simpa [mul_assoc] using hbound
  have hExpNonneg : 0 ≤ Real.exp (Cξ * A₂ ^ 6) := (Real.exp_pos _).le
  have hrealBound : (∫ x in originCube (d := d) (3 / 4), v x) ≤
      Real.exp (Cξ * A₂ ^ 6) :=
    (ENNReal.ofReal_le_ofReal_iff hExpNonneg).mp hbound'
  exact ⟨integral_nonneg_of_ae hposSmall, hrealBound⟩

/-- Adapt the scalar Bombieri estimate (`l.bombieri`), stated for measurable inputs, to an
integrable function, which is only almost everywhere measurable in the argument. -/
theorem bombieri_integral_bound_of_integrable_log_eLpNorm {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ Cξ : ℝ, 0 < Cξ ∧
      ∀ (d : ℕ) (A₂ : ℝ), 1 ≤ A₂ →
        ∀ v : Vec d → ℝ,
          (∀ᵐ x ∂(volume.restrict (originCube (d := d) (7 / 8))), 0 < v x) →
          IntegrableOn v (originCube (d := d) (7 / 8)) →
          eLpNorm (fun x => Real.log (v x)) 1
            (volume.restrict (originCube (d := d) (7 / 8))) ≤ ENNReal.ofReal 1 →
          (∀ b : ℝ, 0 < b → b < 1 →
            ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
              eLpNorm v 1 (volume.restrict (originCube ρ)) ≤
                (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) *
                  eLpNorm v (ENNReal.ofReal b) (volume.restrict (originCube R))) →
          (0 ≤ ∫ x in originCube (d := d) (3 / 4), v x ∧
            (∫ x in originCube (d := d) (3 / 4), v x) ≤
              Real.exp (Cξ * A₂ ^ 6)) := by
  obtain ⟨Cξ, hCξ, hscalar⟩ := bombieri_integral_bound_of_log_eLpNorm hξ
  refine ⟨Cξ, hCξ, ?_⟩
  intro d A₂ hA₂ v hpos hint hlog hrev
  let V := originCube (d := d) (7 / 8)
  let μ := volume.restrict V
  change Integrable v μ at hint
  have hvAEM : AEMeasurable v μ := hint.aemeasurable
  let w : Vec d → ℝ := hvAEM.mk v
  have hw : Measurable w := hvAEM.measurable_mk
  have hEq : v =ᵐ[μ] w := hvAEM.ae_eq_mk
  have hwpos : ∀ᵐ x ∂μ, 0 < w x := by
    filter_upwards [hEq, hpos] with x hx hpx
    rw [← hx]
    exact hpx
  have hwint : Integrable w μ := hint.congr hEq
  have hlogEq : (fun x => Real.log (w x)) =ᵐ[μ]
      (fun x => Real.log (v x)) := by
    exact hEq.symm.mono fun _ hx => congrArg Real.log hx
  have hwlog : eLpNorm (fun x => Real.log (w x)) 1 μ ≤ ENNReal.ofReal 1 := by
    rw [eLpNorm_congr_ae hlogEq]
    exact hlog
  have hwlog' : eLpNorm (fun x => Real.log (w x)) 1 μ ≤ 1 := by
    simpa using hwlog
  have hrevW : ∀ b : ℝ, 0 < b → b < 1 →
      ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
        eLpNorm w 1 (volume.restrict (originCube ρ)) ≤
          (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) *
            eLpNorm w (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
    intro b hb hb1 ρ R hρ hρR hR
    have hsubρ : originCube ρ ⊆ V :=
      Harnack.Scalar.originCube_subset_of_le (le_trans hρR.le hR)
    have hsubR : originCube R ⊆ V := Harnack.Scalar.originCube_subset_of_le hR
    have hμρ : volume.restrict (originCube ρ) ≤ μ :=
      Measure.restrict_mono hsubρ le_rfl
    have hμR : volume.restrict (originCube R) ≤ μ :=
      Measure.restrict_mono hsubR le_rfl
    have hEqρ : w =ᵐ[volume.restrict (originCube ρ)] v := ae_mono hμρ hEq.symm
    have hEqR : w =ᵐ[volume.restrict (originCube R)] v := ae_mono hμR hEq.symm
    rw [eLpNorm_congr_ae hEqρ, eLpNorm_congr_ae hEqR]
    exact hrev b hb hb1 ρ R hρ hρR hR
  have hbound := hscalar d A₂ hA₂ w (hw.comp measurable_subtype_coe)
    hwpos (by change IntegrableOn w V; exact hwint) hwlog' hrevW
  rcases hbound with ⟨hbound0, hbound⟩
  have hsubset : originCube (d := d) (3 / 4) ⊆ V :=
    Harnack.Scalar.originCube_subset_of_le (by norm_num)
  have hμsmall : volume.restrict (originCube (d := d) (3 / 4)) ≤ μ :=
    Measure.restrict_mono hsubset le_rfl
  have hintSmall : Integrable v (volume.restrict (originCube (d := d) (3 / 4))) :=
    hint.mono_measure hμsmall
  have hwintSmall : Integrable w (volume.restrict (originCube (d := d) (3 / 4))) :=
    hwint.mono_measure hμsmall
  have hposSmall : ∀ᵐ x ∂(volume.restrict (originCube (d := d) (3 / 4))),
      0 ≤ v x := by
    have hposSmall' := hpos.filter_mono (ae_mono hμsmall)
    filter_upwards [hposSmall'] with x hx
    exact hx.le
  have hEqSmall : w =ᵐ[volume.restrict (originCube (d := d) (3 / 4))] v :=
    ae_mono hμsmall hEq.symm
  have hEqIntegral : (∫ x in originCube (d := d) (3 / 4), w x) =
      (∫ x in originCube (d := d) (3 / 4), v x) :=
    integral_congr_ae hEqSmall
  rw [hEqIntegral] at hbound
  exact ⟨integral_nonneg_of_ae hposSmall, hbound⟩

end

end CoarseDeGiorgi.Harnack.CrossoverFinal
