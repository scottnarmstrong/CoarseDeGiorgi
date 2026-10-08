module

public import CoarseDeGiorgi.Weighted.L1Tools

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A measurable energy limit of finite-energy fields has finite energy. -/
theorem energy_lt_top_of_tendsto (ha : IsWeightedCoeffOn V a)
    {F : ℕ → Vec d → Vec d} {G : Vec d → Vec d}
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEF : ∀ n, weightedEnergy a V (F n) < ⊤)
    (ht : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (nhds 0)) :
    weightedEnergy a V G < ⊤ := by
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 1 zero_lt_one).exists
  have hdiff : weightedEnergy a V (-(F n - G)) < ⊤ := by
    rw [energy_neg]
    exact hn.trans ENNReal.one_lt_top
  have heq : G = F n + -(F n - G) := by abel
  rw [heq]
  exact energy_add_lt_top ha (hF n) ((hF n).sub hG).neg (hEF n) hdiff

/-- Energy controls each coordinate L¹ seminorm. -/
theorem coord_l1_le_energy (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hE : weightedEnergy a V G < ⊤) (i : Fin d) :
    eLpNorm (fun x => G x i) 1 (volume.restrict V) ≤
      ENNReal.ofReal (Real.sqrt (∫ x in V, ((a x)⁻¹).trace) *
        Real.sqrt (weightedEnergy a V G).toReal) := by
  have hl := gradient_length_integrable_and_bound ha hG hE
  have hi := coord_integrable_of_length hG hl.1 i
  rw [l1_eq_ofReal_integral_abs hi]
  apply ENNReal.ofReal_le_ofReal
  refine (integral_mono_ae hi.abs hl.1 ?_).trans hl.2
  filter_upwards with x
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_apply_le_vecNormSq (G x) i)

/-- Energy convergence implies coordinate L¹ convergence. -/
theorem tendsto_coord_l1_of_energy (ha : IsWeightedCoeffOn V a)
    {F : ℕ → Vec d → Vec d} {G : Vec d → Vec d}
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEF : ∀ n, weightedEnergy a V (F n) < ⊤)
    (ht : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (nhds 0)) (i : Fin d) :
    Tendsto (fun n => eLpNorm (fun x => F n x i - G x i) 1 (volume.restrict V))
      atTop (nhds 0) := by
  have hEG := energy_lt_top_of_tendsto ha hF hG hEF ht
  have hdiff (n : ℕ) : weightedEnergy a V (F n - G) < ⊤ := by
    simpa only [sub_eq_add_neg, energy_neg] using
      energy_add_lt_top ha (hF n) hG.neg (hEF n) (by rw [energy_neg]; exact hEG)
  have hreal : Tendsto (fun n => (weightedEnergy a V (F n - G)).toReal) atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp ht
  have hs : Tendsto (fun n => Real.sqrt (weightedEnergy a V (F n - G)).toReal)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hreal
  have hb : Tendsto (fun n => ENNReal.ofReal
      (Real.sqrt (∫ x in V, ((a x)⁻¹).trace) * Real.sqrt (weightedEnergy a V (F n - G)).toReal))
      atTop (nhds 0) := by
    have hm := hs.const_mul (Real.sqrt (∫ x in V, ((a x)⁻¹).trace))
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fun n => coord_l1_le_energy ha ((hF n).sub hG) (hdiff n) i)

end CoarseDeGiorgi.Weighted
