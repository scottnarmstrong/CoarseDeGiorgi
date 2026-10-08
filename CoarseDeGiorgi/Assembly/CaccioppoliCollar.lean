import CoarseDeGiorgi.Assembly.CaccioppoliParameters
import Mathlib.Algebra.Order.Archimedean.Basic

namespace CoarseDeGiorgi.Assembly

/-- A triadic width within a factor of three of any positive target. -/
theorem caccioppoli_triadic_width {H : ℝ} (hH : 0 < H) :
    ∃ n : ℤ, (3 : ℝ) ^ n ≤ H ∧ H < 3 * (3 : ℝ) ^ n := by
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow hH (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, hn.1, ?_⟩
  simpa only [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, mul_comm] using hn.2

/-- A conservative collar choice obeys the geometric constraint and both source powers.
Taking a smaller width than the minimum in the source changes only its parameter constant. -/
theorem caccioppoli_collar {δ D Z Θ θ γ m : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hD : 0 < D) (hZ : D ≤ Z)
    (hΘ : 0 ≤ Θ) (hθ : 0 < θ) (hγ : θ ≤ γ) (hm : 0 ≤ m) :
    ∃ n : ℤ, (3 : ℝ) ^ n ≤ δ / D ∧
      ((3 : ℝ) ^ n) ^ θ ≤ δ ^ γ * (1 + Θ) ^ (-1 / 2 : ℝ) * Z ^ (-θ) ∧
      ((3 : ℝ) ^ n) ^ (-2 * m) ≤
        (3 * Z) ^ (2 * m) * δ ^ (-2 * γ * m / θ) * (1 + Θ) ^ (m / θ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le hD hZ
  have hT : 0 < 1 + Θ := by linarith only [hΘ]
  let H := δ ^ (γ / θ) * (1 + Θ) ^ (-1 / (2 * θ)) * Z⁻¹
  have hH : 0 < H := mul_pos
    (mul_pos (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hT _)) (inv_pos.mpr hZ0)
  obtain ⟨n, hn, hn3⟩ := caccioppoli_triadic_width hH
  have hh : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hratio : 1 ≤ γ / θ := (le_div_iff₀ hθ).mpr (by simpa using hγ)
  have hpow : δ ^ (γ / θ) ≤ δ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hratio
  have hΘpow : (1 + Θ) ^ (-1 / (2 * θ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hΘ])
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  have hwidth : H ≤ δ / D := by
    calc
      H ≤ δ * 1 * Z⁻¹ := mul_le_mul_of_nonneg_right
        (mul_le_mul hpow hΘpow (Real.rpow_pos_of_pos hT _).le hδ.le) (inv_nonneg.mpr hZ0.le)
      _ ≤ δ / D := by
        simp only [mul_one, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hD hZ) hδ.le
  have hpower : H ^ θ = δ ^ γ * (1 + Θ) ^ (-1 / 2 : ℝ) * Z ^ (-θ) := by
    dsimp [H]
    rw [Real.mul_rpow (by positivity) (inv_nonneg.mpr hZ0.le),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hδ.le, ← Real.rpow_mul hT.le, Real.inv_rpow hZ0.le,
      ← Real.rpow_neg hZ0.le]
    congr 2 <;> field_simp
  have hneg : (H / 3) ^ (-2 * m) =
      (3 * Z) ^ (2 * m) * δ ^ (-2 * γ * m / θ) * (1 + Θ) ^ (m / θ) := by
    have heq : H / 3 = δ ^ (γ / θ) * (1 + Θ) ^ (-1 / (2 * θ)) * (3 * Z)⁻¹ := by
      dsimp [H]
      field_simp
    rw [heq, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hδ.le, ← Real.rpow_mul hT.le,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_mul]
    have h1 : γ / θ * -(2 * m) = -2 * γ * m / θ := by ring
    have h2 : -1 / (2 * θ) * -(2 * m) = m / θ := by field_simp
    rw [h1, h2, neg_neg]
    ring
  refine ⟨n, hn.trans hwidth, ?_, ?_⟩
  · exact (Real.rpow_le_rpow hh.le hn hθ.le).trans_eq hpower
  · apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < H / 3)
      (by linarith only [hn3] : H / 3 ≤ (3 : ℝ) ^ n) (by linarith only [hm])).trans_eq hneg


/-- Young absorption in the normalization used by the one-surface estimate. -/
theorem caccioppoli_young {ε E A : ℝ} (hε : 0 < ε) (hE : 0 ≤ E) :
    A * Real.sqrt E ≤ ε * E + A ^ 2 / (4 * ε) := by
  have h4 : 0 < 4 * ε := by positivity
  have hs := sq_nonneg (2 * ε * Real.sqrt E - A)
  rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt hE] at hs
  apply (mul_le_mul_iff_right₀ h4).mp
  rw [mul_add, mul_div_cancel₀ _ h4.ne']
  nlinarith only [hs]


end CoarseDeGiorgi.Assembly
