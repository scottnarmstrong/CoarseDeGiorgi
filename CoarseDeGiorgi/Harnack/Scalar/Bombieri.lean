import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Harnack.Scalar.BombieriCore

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

/-- Lemma `l.bombieri`: a bound on `log v` and the reverse moment inequalities bound the
integral of `v` over `originCube (3 / 4)` by `exp (C A₁ A₂ ^ 6)`. -/
theorem bombieri_integral_bound_proved (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (A₁ A₂ : ℝ), 1 ≤ A₁ → 1 ≤ A₂ →
        ∀ v : Vec d → ℝ,
          Measurable (fun x : originCube (d := d) (7 / 8) => v x) →
          (∀ᵐ x ∂(volume.restrict (originCube (7 / 8))), 0 < v x) →
          IntegrableOn v (originCube (7 / 8)) →
          eLpNorm (fun x => Real.log (v x)) 1
            (volume.restrict (originCube (7 / 8))) ≤ ENNReal.ofReal A₁ →
          (∀ b : ℝ, 0 < b → b < 1 →
            ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
              eLpNorm v 1 (volume.restrict (originCube ρ)) ≤
                (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) *
                  eLpNorm v (ENNReal.ofReal b) (volume.restrict (originCube R))) →
          eLpNorm v 1 (volume.restrict (originCube (3 / 4))) ≤
            ENNReal.ofReal (Real.exp (C * A₁ * A₂ ^ 6)) := by
  obtain ⟨C, hC, hglobal⟩ := Harnack.Scalar.bombieri_integral_bound_global ξ hξ
  refine ⟨C, hC, ?_⟩
  intro d A₁ A₂ hA₁ hA₂ v hv hpos hvint hlog hrev
  let E := originCube (d := d) (7 / 8)
  let μ₀ : Measure (Vec d) := volume.restrict E
  obtain ⟨w, hw, hEq⟩ := Harnack.Scalar.exists_measurable_extension_originCube hv
  have hEq₀ : w =ᵐ[μ₀] v := by
    filter_upwards [ae_restrict_mem (Harnack.Scalar.measurableSet_originCube (d := d) (7 / 8))]
      with x hx
    exact hEq x hx
  have hposW : ∀ᵐ x ∂μ₀, 0 < w x := by
    filter_upwards [hEq₀, hpos] with x hEqx hx
    rw [hEqx]
    exact hx
  have hwint : IntegrableOn w E := hvint.congr hEq₀.symm
  have hlogEq : (fun x => Real.log (w x)) =ᵐ[μ₀] (fun x => Real.log (v x)) :=
    hEq₀.mono fun _ hxy => congrArg Real.log hxy
  have hlogW : eLpNorm (fun x => Real.log (w x)) 1 μ₀ ≤ ENNReal.ofReal A₁ := by
    rw [eLpNorm_congr_ae hlogEq]
    exact hlog
  have hEq_restrict : ∀ ρ, ρ ≤ 7 / 8 →
      w =ᵐ[volume.restrict (originCube (d := d) ρ)] v := by
    intro ρ hρ
    have hsub : originCube (d := d) ρ ⊆ E :=
      Harnack.Scalar.originCube_subset_of_le hρ
    filter_upwards [ae_restrict_mem (Harnack.Scalar.measurableSet_originCube (d := d) ρ)]
      with x hx
    exact hEq x (hsub hx)
  have hrevW : ∀ b : ℝ, 0 < b → b < 1 →
      ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
        eLpNorm w 1 (volume.restrict (originCube ρ)) ≤
          (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) *
            eLpNorm w (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
    intro b hb hb1 ρ R hρ hρR hR
    have hEqρ := hEq_restrict ρ (le_trans hρR.le hR)
    have hEqR := hEq_restrict R hR
    rw [eLpNorm_congr_ae hEqρ, eLpNorm_congr_ae hEqR]
    exact hrev b hb hb1 ρ R hρ hρR hR
  have hbound := hglobal d A₁ A₂ hA₁ hA₂ w hw hposW hwint hlogW hrevW
  have hEqsmall := hEq_restrict (3 / 4) (by norm_num)
  calc
    eLpNorm v 1 (volume.restrict (originCube (3 / 4))) =
        eLpNorm w 1 (volume.restrict (originCube (3 / 4))) :=
      (eLpNorm_congr_ae hEqsmall).symm
    _ ≤ ENNReal.ofReal (Real.exp (C * A₁ * A₂ ^ 6)) := hbound

end CoarseDeGiorgi
