import CoarseDeGiorgi.Assembly.CaccioppoliAbsorption

namespace CoarseDeGiorgi.Assembly

/-- Absorb the two different radius powers in the hybrid energy estimate.
The constant is chosen before the radius, contrast, energy and level data. -/
theorem hybrid_energy_absorption {C D θ γ η m ε : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hθ : 0 < θ) (hγ : θ ≤ γ)
    (hm : 0 ≤ m) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ δ Θ N E F : ℝ,
      0 < δ → δ ≤ 1 → 0 ≤ Θ → 0 ≤ N → 0 ≤ E →
      (∀ n : ℤ, (3 : ℝ) ^ n ≤ δ / D →
        F ≤ C * δ ^ (-γ) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ * E +
          C * δ ^ (-η) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ (-m) * N * Real.sqrt E) →
      F ≤ ε * E + B * δ ^ (-(2 * η + 2 * γ * m / θ)) *
        (1 + Θ) ^ (1 + m / θ) * N ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := caccioppoli_absorption hC hD hθ hγ hm
    (show 0 < ε / 2 by positivity)
  refine ⟨B, hB, ?_⟩
  intro δ Θ N E F hδ hδ1 hΘ hN hE hsurface
  have hscaled : ∀ n : ℤ, (3 : ℝ) ^ n ≤ δ / D →
      F ≤ C * δ ^ (-γ) *
        (Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ * E +
          Real.sqrt Θ * ((3 : ℝ) ^ n) ^ (-m) *
            (δ ^ (γ - η) * N) * Real.sqrt E) := by
    intro n hn
    apply (hsurface n hn).trans_eq
    have hcancel : δ ^ (-γ) * δ ^ (γ - η) = δ ^ (-η) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = C * δ ^ (-γ) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ * E +
          C * (δ ^ (-γ) * δ ^ (γ - η)) * Real.sqrt Θ *
            ((3 : ℝ) ^ n) ^ (-m) * N * Real.sqrt E := by rw [hcancel]
      _ = _ := by ring
  have h := hbound δ Θ Θ (δ ^ (γ - η) * N) E F hδ hδ1 hΘ hΘ
    (by positivity) hE hscaled
  have hpower : δ ^ (-(2 * γ + 2 * γ * m / θ)) * (δ ^ (γ - η)) ^ 2 =
      δ ^ (-(2 * η + 2 * γ * m / θ)) := by
    rw [← Real.rpow_two (δ ^ (γ - η)), ← Real.rpow_mul hδ.le,
      ← Real.rpow_add hδ]
    congr 1
    ring
  have hcontrast : Θ * (1 + Θ) ^ (m / θ) ≤ (1 + Θ) ^ (1 + m / θ) := by
    calc
      _ ≤ (1 + Θ) * (1 + Θ) ^ (m / θ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [Real.rpow_add (by positivity), Real.rpow_one]
  calc
    F ≤ 2 * (ε / 2) * E + B * δ ^ (-(2 * γ + 2 * γ * m / θ)) *
        Θ * (1 + Θ) ^ (m / θ) * (δ ^ (γ - η) * N) ^ 2 := h
    _ = ε * E + B * δ ^ (-(2 * η + 2 * γ * m / θ)) *
        (Θ * (1 + Θ) ^ (m / θ)) * N ^ 2 := by
      rw [mul_pow]
      have heq : 2 * (ε / 2) = ε := by ring
      rw [heq]
      calc
        _ = ε * E + B *
            (δ ^ (-(2 * γ + 2 * γ * m / θ)) * (δ ^ (γ - η)) ^ 2) *
            (Θ * (1 + Θ) ^ (m / θ)) * N ^ 2 := by ring
        _ = _ := by rw [hpower]
    _ ≤ _ := add_le_add
      (le_refl (ε * E))
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcontrast
          (show 0 ≤ B * δ ^ (-(2 * η + 2 * γ * m / θ)) by positivity))
        (sq_nonneg N))

/-- The collar absorption specialized to the source level powers of Y and Δ. -/
theorem hybrid_energy_level_absorption {C D θ γ η m ε s : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hθ : 0 < θ) (hγ : θ ≤ γ)
    (hm : 0 ≤ m) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ δ Θ Y Δ F : ℝ,
      0 < δ → δ ≤ 1 → 0 ≤ Θ → 0 < Y → 0 < Δ →
      (∀ n : ℤ, (3 : ℝ) ^ n ≤ δ / D →
        F ≤ C * δ ^ (-γ) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ * Y ^ 2 +
          C * δ ^ (-η) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ (-m) *
            Y ^ (1 + s / 2) * Δ ^ (1 - s / 2)) →
      F ≤ ε * Y ^ 2 + B * δ ^ (-(2 * η + 2 * γ * m / θ)) *
        (1 + Θ) ^ (1 + m / θ) * Y ^ s * Δ ^ (2 - s) := by
  obtain ⟨B, hB, hbound⟩ := hybrid_energy_absorption (η := η) hC hD hθ hγ hm hε
  refine ⟨B, hB, ?_⟩
  intro δ Θ Y Δ F hδ hδ1 hΘ hY hΔ hsurface
  have hscaled : ∀ n : ℤ, (3 : ℝ) ^ n ≤ δ / D →
      F ≤ C * δ ^ (-γ) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ * Y ^ 2 +
        C * δ ^ (-η) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ (-m) *
          (Y ^ (s / 2) * Δ ^ (1 - s / 2)) * Real.sqrt (Y ^ 2) := by
    intro n hn
    apply (hsurface n hn).trans_eq
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hY]
    have hp : Y ^ (1 + s / 2) = Y * Y ^ (s / 2) := by
      rw [Real.rpow_add hY, Real.rpow_one]
    rw [hp]
    ring
  have h := hbound δ Θ (Y ^ (s / 2) * Δ ^ (1 - s / 2)) (Y ^ 2) F
    hδ hδ1 hΘ (by positivity) (sq_nonneg Y) hscaled
  have hp : (Y ^ (s / 2) * Δ ^ (1 - s / 2)) ^ 2 = Y ^ s * Δ ^ (2 - s) := by
    rw [mul_pow, ← Real.rpow_two (Y ^ (s / 2)), ← Real.rpow_mul hY.le,
      ← Real.rpow_two (Δ ^ (1 - s / 2)), ← Real.rpow_mul hΔ.le,
      show s / 2 * 2 = s by ring, show (1 - s / 2) * 2 = 2 - s by ring]
  simpa only [hp, mul_assoc] using h

end CoarseDeGiorgi.Assembly
