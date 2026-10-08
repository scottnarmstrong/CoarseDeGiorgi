import CoarseDeGiorgi.Endpoint.Potential.Sums
import CoarseDeGiorgi.Endpoint.Potential.LayerCake

namespace CoarseDeGiorgi.Endpoint.Potential

open scoped ENNReal

/-- From `ofReal K ≤ Z * (ofReal (2K) * m)^(1/2)` to `ofReal K ≤ 2 Z² m`. -/
theorem quad_ineq {K : ℝ} (hK : 0 < K) {Z m : ℝ≥0∞}
    (h : ENNReal.ofReal K ≤ Z * (ENNReal.ofReal (2 * K) * m) ^ (1 / 2 : ℝ)) :
    ENNReal.ofReal K ≤ ENNReal.ofReal 2 * Z ^ 2 * m := by
  have hKpos : ENNReal.ofReal K ≠ 0 := by simpa using hK
  have hsq : ((ENNReal.ofReal (2 * K) * m) ^ (1 / 2 : ℝ)) ^ 2 = ENNReal.ofReal (2 * K) * m := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h2 : ENNReal.ofReal K ^ 2 ≤ Z ^ 2 * (ENNReal.ofReal (2 * K) * m) := by
    calc ENNReal.ofReal K ^ 2 ≤ (Z * (ENNReal.ofReal (2 * K) * m) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = Z ^ 2 * (ENNReal.ofReal (2 * K) * m) := by rw [mul_pow, hsq]
  have h3 : ENNReal.ofReal K * ENNReal.ofReal K ≤
      ENNReal.ofReal K * (ENNReal.ofReal 2 * Z ^ 2 * m) := by
    calc ENNReal.ofReal K * ENNReal.ofReal K = ENNReal.ofReal K ^ 2 := (sq _).symm
      _ ≤ Z ^ 2 * (ENNReal.ofReal (2 * K) * m) := h2
      _ = ENNReal.ofReal K * (ENNReal.ofReal 2 * Z ^ 2 * m) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; ring
  exact (ENNReal.mul_le_mul_iff_right hKpos ENNReal.ofReal_ne_top).1 h3

/-- The dyadic scale of a positive measure at most one. -/
theorem exists_scale {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {y : ℝ} (hy : 1 < y) :
    ∃ N : ℕ, m ≤ (y ^ N)⁻¹ ∧ (y ^ (N + 1))⁻¹ < m := by
  obtain ⟨N, h1, h2⟩ := exists_nat_pow_near (x := m⁻¹) (one_le_inv₀ hm0 |>.2 hm1) hy
  refine ⟨N, ?_, ?_⟩
  · have : 0 < y ^ N := by positivity
    rw [le_inv_comm₀ hm0 this]; exact h1
  · have : 0 < y ^ (N + 1) := by positivity
    rw [inv_lt_comm₀ this hm0]; exact h2

/-- Summation of the level estimates, with the geometric weights of the scales. -/
theorem assembly_bound {d : ℕ} {rs g₁ : ℝ} (hrs : 1 < rs) (hg : g₁ * rs = d)
    (A m : ℝ≥0∞) (c : ℕ → ℝ≥0∞) :
    (∑' N : ℕ, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ N)⁻¹) *
        (ENNReal.ofReal 2 * (A * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * c N) ^ 2 * m) ^ (rs / 2)) ^
        (1 / (rs / 2)) ≤
      ENNReal.ofReal 2 * A ^ 2 * (∑' N, c N) ^ 2 * m := by
  have hη : 0 < rs / 2 := by linarith
  have hterm : ∀ N : ℕ, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ N)⁻¹) *
      (ENNReal.ofReal 2 * (A * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * c N) ^ 2 * m) ^ (rs / 2) =
      (ENNReal.ofReal 2 ^ (rs / 2) * A ^ rs * m ^ (rs / 2)) * c N ^ rs := by
    intro N
    have h3 : ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) ^ rs = ENNReal.ofReal ((3 : ℝ) ^ d) ^ N := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ← Real.rpow_mul (by norm_num), ← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      rw [show g₁ * (N : ℝ) * rs = (g₁ * rs) * N by ring, hg]
    have h4 : ENNReal.ofReal ((((3 : ℝ) ^ d) ^ N)⁻¹) * ENNReal.ofReal ((3 : ℝ) ^ d) ^ N = 1 := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
    have hsq : ((ENNReal.ofReal 2 * (A * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * c N) ^ 2 * m)) ^
        (rs / 2) = ENNReal.ofReal 2 ^ (rs / 2) * (A ^ rs * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) ^ rs
          * c N ^ rs) * m ^ (rs / 2) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hη.le, ENNReal.mul_rpow_of_nonneg _ _ hη.le,
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      rw [show ((2 : ℕ) : ℝ) * (rs / 2) = rs by push_cast; ring]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
    rw [hsq, h3]
    calc _ = (ENNReal.ofReal ((((3 : ℝ) ^ d) ^ N)⁻¹) * ENNReal.ofReal ((3 : ℝ) ^ d) ^ N) *
          (ENNReal.ofReal 2 ^ (rs / 2) * A ^ rs * m ^ (rs / 2)) * c N ^ rs := by ring
      _ = _ := by rw [h4, one_mul]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left]
  have hl := tsum_rpow_le_rpow_tsum c hrs.le
  calc ((ENNReal.ofReal 2 ^ (rs / 2) * A ^ rs * m ^ (rs / 2)) * ∑' N, c N ^ rs) ^ (1 / (rs / 2))
      ≤ ((ENNReal.ofReal 2 ^ (rs / 2) * A ^ rs * m ^ (rs / 2)) * (∑' N, c N) ^ rs) ^
        (1 / (rs / 2)) := by gcongr
    _ = ENNReal.ofReal 2 * A ^ 2 * (∑' N, c N) ^ 2 * m := by
      have hη' : 0 ≤ 1 / (rs / 2) := by positivity
      rw [ENNReal.mul_rpow_of_nonneg _ _ hη', ENNReal.mul_rpow_of_nonneg _ _ hη',
        ENNReal.mul_rpow_of_nonneg _ _ hη', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have e1 : rs / 2 * (1 / (rs / 2)) = 1 := by field_simp
      have e2 : rs * (1 / (rs / 2)) = (2 : ℕ) := by push_cast; field_simp
      rw [e1, e2]
      simp only [ENNReal.rpow_one, ENNReal.rpow_natCast]
      ring

end CoarseDeGiorgi.Endpoint.Potential
