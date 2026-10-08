import CoarseDeGiorgi.Assembly.CaccioppoliCollar

namespace CoarseDeGiorgi.Assembly

/-- The one-surface estimate absorbs into the outer energy with the exact source exponent. -/
theorem caccioppoli_absorption {C D θ γ m ε : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hθ : 0 < θ) (hγ : θ ≤ γ)
    (hm : 0 ≤ m) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ δ Θ Λ N E F : ℝ,
      0 < δ → δ ≤ 1 → 0 ≤ Θ → 0 ≤ Λ → 0 ≤ N → 0 ≤ E →
      (∀ n : ℤ, (3 : ℝ) ^ n ≤ δ / D →
        F ≤ C * δ ^ (-γ) *
          (Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ * E +
            Real.sqrt Λ * ((3 : ℝ) ^ n) ^ (-m) * N * Real.sqrt E)) →
      F ≤ 2 * ε * E + B * δ ^ (-(2 * γ + 2 * γ * m / θ)) *
        Λ * (1 + Θ) ^ (m / θ) * N ^ 2 := by
  let Z := max D (max 1 ((C / ε) ^ (1 / θ)))
  have hDZ : D ≤ Z := le_max_left _ _
  have hZ : 0 < Z := lt_of_lt_of_le hD hDZ
  have hroot : (C / ε) ^ (1 / θ) ≤ Z :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hpow : C / ε ≤ Z ^ θ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (div_nonneg hC hε.le) _) hroot hθ.le
    rw [← Real.rpow_mul (div_nonneg hC hε.le), one_div_mul_cancel hθ.ne', Real.rpow_one] at h
    exact h
  have hsmall : C * Z ^ (-θ) ≤ ε := by
    rw [Real.rpow_neg hZ.le, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr
    have h := (div_le_iff₀ hε).mp hpow
    simpa only [mul_comm] using h
  let B := C ^ 2 / (4 * ε) * (3 * Z) ^ (2 * m)
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro δ Θ Λ N E F hδ hδ1 hΘ hΛ hN hE hsurface
  have hT : 0 < 1 + Θ := by linarith only [hΘ]
  obtain ⟨n, hn, hθn, hmn⟩ := caccioppoli_collar hδ hδ1 hD hDZ hΘ hθ hγ hm
  have hh : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hΘfac : Real.sqrt Θ * (1 + Θ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    calc
      _ ≤ Real.sqrt (1 + Θ) * (1 + Θ) ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith))
          (Real.rpow_nonneg hT.le _)
      _ = 1 := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT]; norm_num
  have ha : C * δ ^ (-γ) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ ≤ ε := by
    calc
      _ ≤ C * δ ^ (-γ) * Real.sqrt Θ *
          (δ ^ γ * (1 + Θ) ^ (-1 / 2 : ℝ) * Z ^ (-θ)) :=
        mul_le_mul_of_nonneg_left hθn (by positivity)
      _ = C * Z ^ (-θ) * (Real.sqrt Θ * (1 + Θ) ^ (-1 / 2 : ℝ)) := by
        have hc : δ ^ (-γ) * δ ^ γ = 1 := by rw [← Real.rpow_add hδ]; norm_num
        calc
          _ = C * Z ^ (-θ) * (Real.sqrt Θ * (1 + Θ) ^ (-1 / 2 : ℝ)) *
            (δ ^ (-γ) * δ ^ γ) := by ring
          _ = _ := by rw [hc, mul_one]
      _ ≤ C * Z ^ (-θ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hΘfac (by positivity)
      _ ≤ ε := hsmall
  let A := C * δ ^ (-γ) * Real.sqrt Λ * ((3 : ℝ) ^ n) ^ (-m) * N
  have hAsq : A ^ 2 = C ^ 2 * δ ^ (-2 * γ) * Λ * ((3 : ℝ) ^ n) ^ (-2 * m) * N ^ 2 := by
    dsimp [A]
    simp only [mul_pow, Real.sq_sqrt hΛ]
    rw [← Real.rpow_two (δ ^ (-γ)), ← Real.rpow_mul hδ.le,
      ← Real.rpow_two (((3 : ℝ) ^ n) ^ (-m)), ← Real.rpow_mul hh.le]
    rw [show (-γ) * 2 = -2 * γ by ring, show (-m) * 2 = -2 * m by ring]
  have hb : A ^ 2 / (4 * ε) ≤
      B * δ ^ (-(2 * γ + 2 * γ * m / θ)) * Λ * (1 + Θ) ^ (m / θ) * N ^ 2 := by
    rw [hAsq]
    have hb0 := mul_le_mul_of_nonneg_left hmn
      (show 0 ≤ C ^ 2 * δ ^ (-2 * γ) * Λ by positivity)
    have hb1 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb0 (sq_nonneg N)) (by positivity : 0 ≤ 4 * ε)
    apply hb1.trans_eq
    dsimp [B]
    have hδpow : δ ^ (-2 * γ) * δ ^ (-2 * γ * m / θ) =
        δ ^ (-(2 * γ + 2 * γ * m / θ)) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = (C ^ 2 / (4 * ε) * (3 * Z) ^ (2 * m)) *
          (δ ^ (-2 * γ) * δ ^ (-2 * γ * m / θ)) * Λ * (1 + Θ) ^ (m / θ) * N ^ 2 := by ring
      _ = _ := by rw [hδpow]
  have hy := caccioppoli_young hε hE (A := A)
  calc
    F ≤ C * δ ^ (-γ) *
        (Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ * E +
          Real.sqrt Λ * ((3 : ℝ) ^ n) ^ (-m) * N * Real.sqrt E) := hsurface n hn
    _ = (C * δ ^ (-γ) * Real.sqrt Θ * ((3 : ℝ) ^ n) ^ θ) * E + A * Real.sqrt E := by
      dsimp [A]
      ring
    _ ≤ ε * E + (ε * E + A ^ 2 / (4 * ε)) :=
      add_le_add (mul_le_mul_of_nonneg_right ha hE) hy
    _ ≤ 2 * ε * E + B * δ ^ (-(2 * γ + 2 * γ * m / θ)) *
        Λ * (1 + Θ) ^ (m / θ) * N ^ 2 := by linarith only [hb]


end CoarseDeGiorgi.Assembly
