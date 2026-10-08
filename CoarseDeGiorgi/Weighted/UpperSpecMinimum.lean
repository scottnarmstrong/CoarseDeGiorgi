import CoarseDeGiorgi.Weighted.UpperSpecHarmonic

namespace CoarseDeGiorgi.Weighted.UpperResponseImpl

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The selected response is the least energy in the literal affine boundary class. -/
theorem upper_affine_minimum (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    IsLeast
      {v : ℝ | ∃ h : Vec d → ℝ, ∃ Gh : Vec d → Vec d,
        MemH1a a V h Gh ∧
        MemH1a0 a V (fun x => h x - vecDot e x) (fun x => Gh x - e) ∧
        v = volumeAverage V (fun x => vecDot (Gh x) (matVecMul (a x) (Gh x)))}
      (vecDot e (matVecMul (upperResponse a V hV hne ha) e)) := by
  obtain ⟨h, Gh, hh, hb⟩ := upper_affine_replacement hV hne ha e 0
  have henergy := upper_affine_energy hV hne ha e 0 hh hb
  have hb' : MemH1a0 a V (fun x => h x - vecDot e x) (fun x => Gh x - e) := by
    simpa only [add_zero] using hb
  refine ⟨⟨h, Gh, hh.1, hb', henergy⟩, ?_⟩
  intro v hv
  obtain ⟨w, Gw, hw, hw0, rfl⟩ := hv
  by_cases hd : d = 0
  · subst d
    simp [vecDot, volumeAverage]
  · have : NeZero d := ⟨hd⟩
    have hdiff : MemH1a0 a V (w - h) (Gw - Gh) := by
      have hs := hw0.sub hV hne ha hb'
      convert hs using 1 <;> funext x <;> dsimp only [Pi.sub_apply] <;> abel
    have hi := IsWeightedSolution.energy_identity hV hne ha hh hdiff
    have hle : weightedEnergy a V Gh ≤ weightedEnergy a V Gw := by
      rw [hi]
      exact le_self_add
    have hreal := ENNReal.toReal_mono (hw.energy_lt_top hV.isOpen ha).ne hle
    rw [energy_toReal ha hh.1.2.1, energy_toReal ha hw.2.1] at hreal
    rw [henergy]
    exact mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr ENNReal.toReal_nonneg)


end CoarseDeGiorgi.Weighted.UpperResponseImpl
