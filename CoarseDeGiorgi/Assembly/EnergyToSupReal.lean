import CoarseDeGiorgi.Assembly.EnergyToSupStep

namespace CoarseDeGiorgi.Assembly
open scoped ENNReal

/-- The exact finite hybrid recurrence over the reals. -/
theorem energy_to_sup_recurrence_toReal {C T X Z : ℝ≥0∞} {δ Δ ε g a b c : ℝ}
    (hC : C ≠ ⊤) (hT : T ≠ ⊤) (hT0 : T ≠ 0) (hX : X ≠ ⊤) (hX0 : X ≠ 0)
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (hb : Z.rpow 2 ≤ ENNReal.ofReal ε * X.rpow 2 +
      C * (ENNReal.ofReal δ).rpow (-g) *
        (T.rpow a * X.rpow b * (ENNReal.ofReal Δ).rpow (2 - b) +
          X.rpow c * (ENNReal.ofReal Δ).rpow (2 - c))) :
    Z.toReal ^ 2 ≤ ε * X.toReal ^ 2 + C.toReal * δ ^ (-g) *
      (T.toReal ^ a * X.toReal ^ b * Δ ^ (2 - b) + X.toReal ^ c * Δ ^ (2 - c)) := by
  have hδ0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hΔ0 : ENNReal.ofReal Δ ≠ 0 := (ENNReal.ofReal_pos.mpr hΔ).ne'
  have hTp (r : ℝ) : T.rpow r ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hT0 hT
  have hXp (r : ℝ) : X.rpow r ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hX0 hX
  have hΔp (r : ℝ) : (ENNReal.ofReal Δ).rpow r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hΔ0 ENNReal.ofReal_ne_top
  have hδp : (ENNReal.ofReal δ).rpow (-g) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ0 ENNReal.ofReal_ne_top
  have ht1 := ENNReal.mul_ne_top (ENNReal.mul_ne_top (hTp a) (hXp b)) (hΔp (2 - b))
  have ht2 := ENNReal.mul_ne_top (hXp c) (hΔp (2 - c))
  have hc := ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hδp)
    (ENNReal.add_ne_top.mpr ⟨ht1, ht2⟩)
  have he := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := ε)) (hXp 2)
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨he, hc⟩) hb
  rw [ENNReal.toReal_add he hc] at hh
  simp only [ENNReal.toReal_mul] at hh
  rw [ENNReal.toReal_add ht1 ht2] at hh
  simp only [ENNReal.toReal_mul, ENNReal.rpow_eq_pow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofReal hΔ.le] at hh
  simpa only [ENNReal.toReal_ofReal hε, Real.rpow_two] using hh

end CoarseDeGiorgi.Assembly
