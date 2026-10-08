module

public import CoarseDeGiorgi.Whitney.LiftZeroExtension
public import CoarseDeGiorgi.Weighted.Testing

/-! # Testing and the limit of approximation pairings -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
variable {d : ℕ} {V W : Set (Vec d)} {a : CoeffField d}

/-- Weighted energy convergence gives convergence of the interior pairing on
any measurable subdomain. There is no assumption that the lifts converge. -/
theorem lift_interior_pairing_tendsto (ha : IsWeightedCoeffOn V a) (hWV : W ⊆ V)
    (F : ℕ → Vec d → Vec d) (G : Vec d → Vec d)
    (hF : ∀ i, AEStronglyMeasurable (F i) (volume.restrict V))
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hFE : ∀ i, weightedEnergy a V (F i) < ⊤) (hGE : weightedEnergy a V G < ⊤)
    (hconv : Tendsto (fun i => weightedEnergy a V (F i - G)) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ x in W, vecDot (F i x) (matVecMul (a x) (G x))) atTop
      (𝓝 (weightedEnergy a W G).toReal) := by
  let haW := lift_coeff_mono ha hWV
  have hm := Measure.restrict_mono hWV (le_rfl : volume ≤ volume)
  have hEG : weightedEnergy a W G < ⊤ :=
    (lintegral_mono_set hWV).trans_lt hGE
  let K : Weighted.GradientCore haW := ⟨G, hG.mono_measure hm,
    Weighted.quadratic_integrable haW (hG.mono_measure hm) hEG⟩
  let J (i : ℕ) : Weighted.GradientCore haW := ⟨F i, (hF i).mono_measure hm,
    Weighted.quadratic_integrable haW ((hF i).mono_measure hm)
      ((lintegral_mono_set hWV).trans_lt (hFE i))⟩
  have he : Tendsto (fun i => weightedEnergy a W ((J i).field - K.field)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => bot_le) (fun _ => lintegral_mono_set hWV)
  have hi := (Weighted.GradientCore.tendsto_coe_of_energy haW he).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := (K : Weighted.GradientHilbert haW)))
  simp only [Weighted.gradientHilbert_inner_coe] at hi
  have hself : (∫ x in W, vecDot (G x) (matVecMul (a x) (G x))) =
      (weightedEnergy a W G).toReal := (Weighted.energy_toReal haW (hG.mono_measure hm)).symm
  exact hself ▸ hi

end
end CoarseDeGiorgi.Whitney
