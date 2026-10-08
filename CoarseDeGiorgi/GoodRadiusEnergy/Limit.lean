import CoarseDeGiorgi.Harnack.PowerCaccioppoli.ExteriorTraceBound
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.TraceLr

/-! # Passing the pairing bounds to the limit

Only numbers pass to the limit: pairings `P i ≤ |B i|`, with `ofReal |B i| ≤ K₀ (c₁ Fᵢ + c₂ Lᵢ)` and
`Fᵢ, Lᵢ` asymptotically bounded by `F + ε`, `L + ε`. -/

namespace CoarseDeGiorgi.GoodRadiusEnergy

open MeasureTheory Filter Topology
open scoped ENNReal

theorem energy_le_of_pairings {E K₀ c₁ c₂ F L : ℝ≥0∞} (hE : E < ⊤) (hK₀ : K₀ < ⊤)
    (hc₁ : c₁ < ⊤) (hc₂ : c₂ < ⊤) (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (Fi Li : ℕ → ℝ≥0∞) (P B : ℕ → ℝ)
    (hP : Tendsto P atTop (𝓝 E.toReal)) (hPB : ∀ i, P i ≤ |B i|)
    (hB : ∀ i, ENNReal.ofReal |B i| ≤ K₀ * (c₁ * Fi i + c₂ * Li i))
    (htr : F < ⊤ → L < ⊤ → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      Fi i ≤ F + ENNReal.ofReal ε ∧ Li i ≤ L + ENNReal.ofReal ε) :
    E ≤ K₀ * (c₁ * F + c₂ * L) := by
  by_cases hK : K₀ = 0
  · subst hK
    have hz : ∀ i, P i ≤ 0 := fun i => by
      have h := hB i
      rw [zero_mul, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
      exact (hPB i).trans h
    have h0 : E.toReal ≤ 0 := le_of_tendsto' hP hz
    have hE0 : E = 0 := by
      rcases ENNReal.toReal_eq_zero_iff E |>.mp (le_antisymm h0 ENNReal.toReal_nonneg) with h | h
      · exact h
      · exact absurd h hE.ne
    rw [hE0]
    exact zero_le
  · by_cases hF : F < ⊤ ∧ L < ⊤
    · have hclose := Harnack.PowerCaccioppoli.pairing_abs_eventually_close_of_ennreal_trace_bounds
        K₀ c₁ c₂ F L hK₀ hc₁ hc₂ hF.1 hF.2 Fi Li (htr hF.1 hF.2) B hB
      have hB₀ : K₀ * (c₁ * F + c₂ * L) < ⊤ :=
        ENNReal.mul_lt_top hK₀ (ENNReal.add_lt_top.mpr
          ⟨ENNReal.mul_lt_top hc₁ hF.1, ENNReal.mul_lt_top hc₂ hF.2⟩)
      have hle : E.toReal ≤ (K₀ * (c₁ * F + c₂ * L)).toReal := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        refine le_of_tendsto hP ?_
        filter_upwards [hclose ε hε] with i hi
        exact (hPB i).trans hi
      exact (ENNReal.toReal_le_toReal hE.ne hB₀.ne).mp hle
    · have htop : c₁ * F + c₂ * L = ⊤ := by
        rw [ENNReal.add_eq_top]
        rcases not_and_or.mp hF with h | h
        · left
          exact ENNReal.mul_eq_top.mpr (Or.inl ⟨hc₁0, not_lt_top_iff.mp h⟩)
        · right
          exact ENNReal.mul_eq_top.mpr (Or.inl ⟨hc₂0, not_lt_top_iff.mp h⟩)
      rw [htop]
      rw [ENNReal.mul_top hK]
      exact le_top

end CoarseDeGiorgi.GoodRadiusEnergy
