module

public import CoarseDeGiorgi.Assembly.CaccioppoliParameters
public import CoarseDeGiorgi.Whitney.LiftCell
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Radius elimination in the two-sided energy estimate on one surface. -/

@[expose] public section

namespace CoarseDeGiorgi.Assembly
open scoped ENNReal
noncomputable section

/-- Eliminate the radius after multiplying the three selected controls.
The arbitrary ENNReal moments include an infinite lower moment. -/
theorem two_sided_uniform_eliminate {δ h θ m γ : ℝ}
    (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (_hh : 0 < h) (hh1 : h ≤ 1)
    (hθ : 0 ≤ θ) (hm : 0 ≤ m)
    {K U L E N X : ℝ≥0∞}
    (hbound : X ≤ K * ENNReal.ofReal δ ^ (-γ) * U ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal h ^ θ * (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N) +
        ENNReal.ofReal h ^ (-m) * N)) :
    X ≤ (2 * K) * ENNReal.ofReal δ ^ (-γ) *
      ((U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ θ * E +
        U ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ (-m) * N * E ^ (1 / 2 : ℝ)) := by
  have hpow : ENNReal.ofReal h ^ θ ≤ ENNReal.ofReal h ^ (-m) :=
    ENNReal.rpow_le_rpow_of_exponent_ge
      (by simpa using ENNReal.ofReal_le_ofReal hh1) (by linarith only [hθ, hm])
  have he : E ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) = E := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hc : (U / L) ^ (1 / 2 : ℝ) = U ^ (1 / 2 : ℝ) * L ^ (-1 / 2 : ℝ) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), div_eq_mul_inv]
    congr 1
    simpa only [neg_div] using (ENNReal.rpow_neg L (1 / 2 : ℝ)).symm
  let A := (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ θ * E
  let B := U ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ (-m) * N * E ^ (1 / 2 : ℝ)
  have hx : X ≤ K * ENNReal.ofReal δ ^ (-γ) * (A + B + B) := by
    apply hbound.trans
    calc
      _ = K * ENNReal.ofReal δ ^ (-γ) * (A +
        U ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ θ * N * E ^ (1 / 2 : ℝ) + B) := by
        dsimp [A, B]
        rw [hc]
        ring_nf
        rw [show (E ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = E by simpa only [pow_two] using he]
        ring
      _ ≤ _ := by dsimp [B]; gcongr
  apply hx.trans
  have hab : A + B + B ≤ 2 * (A + B) := by
    calc
      A + B + B ≤ A + A + B + B := by gcongr; exact le_add_right le_rfl
      _ = 2 * (A + B) := by ring
  calc
    _ ≤ K * ENNReal.ofReal δ ^ (-γ) * (2 * (A + B)) := by gcongr
    _ = _ := by dsimp [A, B]; ring

/-- Combine the three selected controls before the final width comparison. -/
theorem two_sided_uniform_multiply {δ h θ m a b γ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 1 / 2 ≤ b)
    (hexp : a + 1 / 2 + b = γ)
    {Kseed Ks Kf Kl S F Z D U L E N X : ℝ≥0∞}
    (hS : S ≤ Ks * ENNReal.ofReal δ ^ (-a) * U ^ (1 / 2 : ℝ))
    (hF : F ≤ Kf * ENNReal.ofReal δ ^ (-b) * (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N))
    (hZ : Z ≤ Kl * ENNReal.ofReal δ ^ (-1 / 2 : ℝ) * N)
    (hD : D ≤ 192 * (ENNReal.ofReal δ)⁻¹ * E)
    (hbound : X ≤ Kseed * S * D ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal h ^ θ * F + ENNReal.ofReal h ^ (-m) * Z)) :
    X ≤ (Kseed * Ks * (192 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (Kf + Kl)) *
      ENNReal.ofReal δ ^ (-γ) * U ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal h ^ θ * (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N) +
        ENNReal.ofReal h ^ (-m) * N) := by
  let P := ENNReal.ofReal δ
  have hP0 : P ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP1 : P ≤ 1 := by simpa [P] using ENNReal.ofReal_le_ofReal hδ1
  have hD' : D ^ (1 / 2 : ℝ) ≤ (192 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
      P ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by
    apply (ENNReal.rpow_le_rpow hD (by norm_num)).trans_eq
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.inv_rpow]
    simp only [P, ← ENNReal.rpow_neg, neg_div]
  have hZ' : Z ≤ Kl * P ^ (-b) * N :=
    hZ.trans (mul_le_mul' (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow_of_exponent_ge hP1 (by linarith only [hb]))) le_rfl)
  have hsum : ENNReal.ofReal h ^ θ * F + ENNReal.ofReal h ^ (-m) * Z ≤
      (Kf + Kl) * P ^ (-b) *
        (ENNReal.ofReal h ^ θ * (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N) +
          ENNReal.ofReal h ^ (-m) * N) := by
    calc
      _ ≤ ENNReal.ofReal h ^ θ * ((Kf + Kl) * P ^ (-b) *
          (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N)) +
          ENNReal.ofReal h ^ (-m) * ((Kf + Kl) * P ^ (-b) * N) := by
        apply add_le_add
        · apply mul_le_mul_right
          exact hF.trans (by gcongr; exact le_add_right le_rfl)
        · apply mul_le_mul_right
          exact hZ'.trans (by gcongr; exact le_add_left le_rfl)
      _ = _ := by ring
  have hp : P ^ (-a) * P ^ (-1 / 2 : ℝ) * P ^ (-b) = P ^ (-γ) := by
    rw [← ENNReal.rpow_add _ _ hP0 hPt, ← ENNReal.rpow_add _ _ hP0 hPt]
    congr 1
    linarith only [hexp]
  apply hbound.trans
  calc
    _ ≤ Kseed * (Ks * P ^ (-a) * U ^ (1 / 2 : ℝ)) *
        ((192 : ℝ≥0∞) ^ (1 / 2 : ℝ) * P ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) *
        ((Kf + Kl) * P ^ (-b) *
          (ENNReal.ofReal h ^ θ * (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N) +
            ENNReal.ofReal h ^ (-m) * N)) := by gcongr
    _ = _ := by
      calc
        _ = (Kseed * Ks * (192 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (Kf + Kl)) *
          (P ^ (-a) * P ^ (-1 / 2 : ℝ) * P ^ (-b)) * U ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal h ^ θ * (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N) +
            ENNReal.ofReal h ^ (-m) * N) := by ring
        _ = _ := by rw [hp]

end
end CoarseDeGiorgi.Assembly
