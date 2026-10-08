import CoarseDeGiorgi.Whitney.Extension.EnergyCube

namespace CoarseDeGiorgi.WhitneyExt

variable {d : ℕ}

theorem mLow_inv_rpow (hd : 1 ≤ d) {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) :
    ((mLow d ℓ)⁻¹) ^ r =
      (100 * (d : ℝ) ^ 2) ^ (((d : ℝ) - 1) * r) / ℓ ^ (((d : ℝ) - 1) * r) := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hA : 0 < 100 * (d : ℝ) ^ 2 := by positivity
  have : (mLow d ℓ)⁻¹ = (100 * (d : ℝ) ^ 2 / ℓ) ^ (d - 1) := by
    unfold mLow; rw [← inv_pow, inv_div]
  rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Nat.cast_sub hd,
    Real.div_rpow hA.le hℓ.le]
  simp

theorem Ra_eq (hd : 1 ≤ d) {b ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) :
    Ra d b ℓ h = 8 * (C32 d + 1) ^ 2 * (100 * (d : ℝ) ^ 2) ^ (((d : ℝ) - 1) * (2 / b)) *
      h⁻¹ ^ 2 * ℓ ^ ((d : ℝ) - ((d : ℝ) - 1) * (2 / b)) := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold Ra
  rw [mLow_inv_rpow hd hℓ, Real.rpow_sub hℓ, Real.rpow_natCast]
  field_simp
  ring

theorem Rb_eq (hd : 1 ≤ d) {α ξ ℓ : ℝ} (hℓ : 0 < ℓ) :
    Rb d α ξ ℓ = 2 * (C32 d + 1) ^ 2 *
      (100 * (d : ℝ) ^ 2) ^ (((d : ℝ) - 1) * (2 * (2 / ξ))) *
      (2 * Real.sqrt (d : ℝ)) ^ (((d : ℝ) - 1 + α * ξ) * (2 / ξ)) *
      ℓ ^ ((d : ℝ) - 2 - ((d : ℝ) - 1) * (2 * (2 / ξ)) + ((d : ℝ) - 1 + α * ξ) * (2 / ξ)) := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hm : 0 < (mLow d ℓ)⁻¹ := inv_pos.2 (mLow_pos d hℓ hd)
  have hB : 0 < 2 * Real.sqrt (d : ℝ) := by positivity
  have h2 : ((mLow d ℓ)⁻¹) ^ 2 = ((mLow d ℓ)⁻¹) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
  unfold Rb
  rw [h2, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hm.le,
    ← Real.rpow_mul (by positivity), mLow_inv_rpow hd hℓ, Real.mul_rpow hB.le hℓ.le,
    ]
  rw [Real.rpow_add hℓ, Real.rpow_sub hℓ, Real.rpow_sub hℓ, Real.rpow_natCast, Real.rpow_two]
  field_simp

theorem three_zpow_one_sub (j : ℕ) (x : ℝ) :
    ((3 : ℝ) ^ ((1 : ℤ) - (j : ℤ))) ^ x = (3 : ℝ) ^ (((1 : ℝ) - j) * x) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  push_cast; rfl

theorem three_zpow_neg (j : ℕ) : (3 : ℝ) ^ (-(j : ℤ)) = (3 : ℝ) ^ (-(j : ℝ)) := by
  rw [← Real.rpow_intCast]; push_cast; rfl

theorem three_zpow_nat (j : ℕ) : (3 : ℝ) ^ (j : ℤ) = (3 : ℝ) ^ (j : ℝ) := by
  rw [← Real.rpow_intCast]; push_cast; rfl

theorem Ra_scale (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) (Nr : ℝ) (hN : 0 ≤ Nr) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (j : ℕ) {h : ℝ}, 0 < h →
      Ra d b ((3 : ℝ) ^ ((1 : ℤ) - (j : ℤ))) h * Nr ^ (2 / b) =
        κ * (3 : ℝ) ^ (-(j : ℤ)) *
          (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) * (((d : ℝ) - 1) * (1 / b - 1 / 2)))) ^ 2 := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨8 * (C32 d + 1) ^ 2 * (100 * (d : ℝ) ^ 2) ^ (((d : ℝ) - 1) * (2 / b)) *
    (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - 1) * (2 / b)) * Nr ^ (2 / b), ?_, ?_⟩
  · have := C32_nonneg d
    positivity
  · intro j h hh
    have hℓ : 0 < (3 : ℝ) ^ ((1 : ℤ) - (j : ℤ)) := by positivity
    rw [Ra_eq hd hℓ hh, three_zpow_one_sub, three_zpow_neg]
    have key : (3 : ℝ) ^ (((1 : ℝ) - j) * ((d : ℝ) - ((d : ℝ) - 1) * (2 / b))) =
        (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - 1) * (2 / b)) *
          ((3 : ℝ) ^ (-(j : ℝ)) *
            ((3 : ℝ) ^ ((j : ℝ) * (((d : ℝ) - 1) * (1 / b - 1 / 2)))) ^ 2) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ ((j : ℝ) * (((d : ℝ) - 1) * (1 / b - 1 / 2)))) 2,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1; push_cast; field_simp; ring
    rw [key, mul_pow]
    ring

theorem Rb_scale (hd : 1 ≤ d) {α ξ : ℝ} (hξ : 0 < ξ) (Nr : ℝ) (hN : 0 ≤ Nr) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (j : ℕ),
      Rb d α ξ ((3 : ℝ) ^ ((1 : ℤ) - (j : ℤ))) * Nr ^ (2 / ξ) =
        κ * (3 : ℝ) ^ (-(j : ℤ)) *
          ((3 : ℝ) ^ (j : ℤ) *
            (3 : ℝ) ^ (-((j : ℝ) * (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2))))) ^ 2 := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by linarith)
  refine ⟨2 * (C32 d + 1) ^ 2 *
      (100 * (d : ℝ) ^ 2) ^ (((d : ℝ) - 1) * (2 * (2 / ξ))) *
      (2 * Real.sqrt (d : ℝ)) ^ (((d : ℝ) - 1 + α * ξ) * (2 / ξ)) *
      (3 : ℝ) ^ ((d : ℝ) - 2 - ((d : ℝ) - 1) * (2 * (2 / ξ)) +
        ((d : ℝ) - 1 + α * ξ) * (2 / ξ)) * Nr ^ (2 / ξ), ?_, ?_⟩
  · have := C32_nonneg d
    positivity
  · intro j
    have hℓ : 0 < (3 : ℝ) ^ ((1 : ℤ) - (j : ℤ)) := by positivity
    rw [Rb_eq hd hℓ, three_zpow_one_sub, three_zpow_neg, three_zpow_nat]
    have key : (3 : ℝ) ^ (((1 : ℝ) - j) * ((d : ℝ) - 2 - ((d : ℝ) - 1) * (2 * (2 / ξ)) +
        ((d : ℝ) - 1 + α * ξ) * (2 / ξ))) =
        (3 : ℝ) ^ ((d : ℝ) - 2 - ((d : ℝ) - 1) * (2 * (2 / ξ)) +
        ((d : ℝ) - 1 + α * ξ) * (2 / ξ)) *
          ((3 : ℝ) ^ (-(j : ℝ)) *
            ((3 : ℝ) ^ (j : ℝ) *
              (3 : ℝ) ^ (-((j : ℝ) * (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2))))) ^ 2) := by
      rw [← Real.rpow_natCast
        ((3 : ℝ) ^ (j : ℝ) * (3 : ℝ) ^ (-((j : ℝ) * (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2)))))
        2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3) (j : ℝ),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1; push_cast; field_simp; ring
    rw [key]
    ring

end CoarseDeGiorgi.WhitneyExt
