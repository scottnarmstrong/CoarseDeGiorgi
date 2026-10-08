module

public import CoarseDeGiorgi.Assembly.HybridAbsorption
public import Mathlib.Tactic

@[expose] public section

namespace CoarseDeGiorgi.Assembly
open scoped ENNReal

/-- Finite source quantities pass through the real collar absorption without
changing any exponent or the order in which the constant is chosen. -/
theorem hybrid_energy_level_absorption_enn {C : ℝ≥0∞} {D θ γ η m ε s : ℝ}
    (hC : C ≠ ⊤) (hD : 0 < D) (hθ : 0 < θ) (hγ : θ ≤ γ)
    (hm : 0 ≤ m) (hε : 0 < ε) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ (δ Δ : ℝ) (Θ Y F : ℝ≥0∞),
      0 < δ → δ ≤ 1 → 0 < Δ → Θ ≠ ⊤ → Y ≠ ⊤ → Y ≠ 0 → F ≠ ⊤ →
      (∀ n : ℤ, (3 : ℝ) ^ n ≤ δ / D →
        F ≤ C * (ENNReal.ofReal δ) ^ (-γ) * Θ ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal ((3 : ℝ) ^ n)) ^ θ * Y ^ (2 : ℝ) +
          C * (ENNReal.ofReal δ) ^ (-η) * Θ ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal ((3 : ℝ) ^ n)) ^ (-m) *
            Y ^ (1 + s / 2) * (ENNReal.ofReal Δ) ^ (1 - s / 2)) →
      F ≤ ENNReal.ofReal ε * Y ^ (2 : ℝ) +
        B * (ENNReal.ofReal δ) ^ (-(2 * η + 2 * γ * m / θ)) *
          (1 + Θ) ^ (1 + m / θ) * Y ^ s * (ENNReal.ofReal Δ) ^ (2 - s) := by
  obtain ⟨B, hB, hbound⟩ := hybrid_energy_level_absorption (η := η) (s := s)
    C.toReal_nonneg hD hθ hγ hm hε
  refine ⟨ENNReal.ofReal B, ENNReal.ofReal_lt_top, ?_⟩
  intro δ Δ Θ Y F hδ hδ1 hΔ hΘ hY hY0 hF hsurf
  have hYpos : 0 < Y.toReal := ENNReal.toReal_pos hY0 hY
  have hδ0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hΔ0 : ENNReal.ofReal Δ ≠ 0 := (ENNReal.ofReal_pos.mpr hΔ).ne'
  have hδfin (a : ℝ) : (ENNReal.ofReal δ) ^ a ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ0 ENNReal.ofReal_ne_top
  have hΔfin (a : ℝ) : (ENNReal.ofReal Δ) ^ a ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hΔ0 ENNReal.ofReal_ne_top
  have hYfin (a : ℝ) : Y ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hY0 hY
  have hΘfin : Θ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΘ
  have hreal : ∀ n : ℤ, (3 : ℝ) ^ n ≤ δ / D →
      F.toReal ≤ C.toReal * δ ^ (-γ) * Real.sqrt Θ.toReal * ((3 : ℝ) ^ n) ^ θ * Y.toReal ^ 2 +
        C.toReal * δ ^ (-η) * Real.sqrt Θ.toReal * ((3 : ℝ) ^ n) ^ (-m) *
          Y.toReal ^ (1 + s / 2) * Δ ^ (1 - s / 2) := by
    intro n hn
    have hh : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
    have hhfin (a : ℝ) : (ENNReal.ofReal ((3 : ℝ) ^ n)) ^ a ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top
    have hleft : C * (ENNReal.ofReal δ) ^ (-γ) * Θ ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal ((3 : ℝ) ^ n)) ^ θ * Y ^ (2 : ℝ) ≠ ⊤ := by finiteness
    have hright : C * (ENNReal.ofReal δ) ^ (-η) * Θ ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal ((3 : ℝ) ^ n)) ^ (-m) * Y ^ (1 + s / 2) *
        (ENNReal.ofReal Δ) ^ (1 - s / 2) ≠ ⊤ := by finiteness
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hleft, hright⟩) (hsurf n hn)
    rw [ENNReal.toReal_add hleft hright] at h
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofReal hh.le, ENNReal.toReal_ofReal hΔ.le,
      ← Real.sqrt_eq_rpow, Real.rpow_two] using h
  have h := hbound δ Θ.toReal Y.toReal Δ F.toReal hδ hδ1 Θ.toReal_nonneg hYpos hΔ hreal
  have hT0 : 1 + Θ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
    (le_add_right le_rfl))
  have hT : 1 + Θ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by norm_num, hΘ⟩
  have hTfin (a : ℝ) : (1 + Θ) ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hT0 hT
  apply (ENNReal.toReal_le_toReal hF (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hε.le,
    ENNReal.toReal_ofReal hB, ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofReal hΔ.le,
    ENNReal.toReal_add (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hΘ, ENNReal.toReal_one,
    Real.rpow_two] using h

end CoarseDeGiorgi.Assembly
