module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessRatio
public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessLowerMoment
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.EuclidNorm
public import CoarseDeGiorgi.Statements.RStarParam

/-! # Sharpness of the weak Harnack exponent

Assembly of the radial field `a(ρ) = ρ^β log³(eR/ρ)` and the supersolutions `u_ε`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem whBeta_pos {d : ℕ} {q t : ℝ} (hq : 0 < q) (ht : 0 < t) : 0 < whBeta d q t := by
  unfold whBeta
  positivity

theorem whBeta_lt {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s)
    (hθ : 0 < paramTheta d p q s t) : whBeta d q t < d := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold paramTheta at hθ
  unfold whBeta
  have hr : 0 < 1 / q := by positivity
  have hr1 : 1 / q < 1 := by rw [div_lt_one (by linarith)]; exact hq
  have hp0 : 0 ≤ ((d : ℝ) - 1) / 2 * (1 / p) := by
    apply mul_nonneg (by linarith) (by positivity)
  have e1 : (d : ℝ) / q = d * (1 / q) := by ring
  have e2 : ((d : ℝ) - 1) / 2 * (1 / p + 1 / q) =
      ((d : ℝ) - 1) / 2 * (1 / p) + ((d : ℝ) * (1 / q) - 1 / q) / 2 := by ring
  rw [e2] at hθ
  rw [e1]
  nlinarith

theorem whRStar_lt {d : ℕ} (hd : 3 ≤ d) {q t : ℝ} (hq : 1 < q) (ht : 0 < t) {η : ℝ}
    (h : rStarParam (d := d) q t / 2 < η) :
    (d : ℝ) < ((d : ℝ) + whBeta d q t - 2) * η := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 < q := by linarith
  have hβ := whBeta_pos (d := d) hq0 ht
  set κ : ℝ := (d : ℝ) + whBeta d q t - 2 with hκ
  have hκ0 : 0 < κ := by linarith
  have hκeq : κ = (d : ℝ) - 2 + 2 * t + d / q := by rw [hκ]; unfold whBeta; ring
  have hden : (d : ℝ) - (1 - t) * (2 * q / (q + 1)) = q * κ / (q + 1) := by
    rw [hκeq]; field_simp; ring
  have key : rStarParam (d := d) q t = 2 * d / κ := by
    unfold rStarParam alphaParam paramR
    simp only
    rw [hden]
    have : q + 1 ≠ 0 := by linarith
    field_simp
  rw [key] at h
  have h2 : (d : ℝ) / κ < η := by
    have : 2 * (d : ℝ) / κ / 2 = d / κ := by ring
    rwa [this] at h
  exact (div_lt_iff₀ hκ0).1 h2 |>.trans_eq (mul_comm _ _)

/-- Sharpness of the weak Harnack exponent. -/
theorem weakHarnackSharpness_proved (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ (a : ℝ → ℝ) (ha : IsWeightedCoeffOn (originCube 1)
        (fun x : Vec d => a (euclidNorm x) • (1 : Mat d))),
      upperMoment (fun x : Vec d => a (euclidNorm x) • (1 : Mat d)) ha s p hs hp.le < ⊤ ∧
      0 < lowerMoment (fun x : Vec d => a (euclidNorm x) • (1 : Mat d)) ha t q ht hq.le ∧
      ∃ (u : ℝ → Vec d → ℝ) (G : ℝ → Vec d → Vec d),
        (∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u ε x) ∧
          IsWeightedSupersolution (fun x : Vec d => a (euclidNorm x) • (1 : Mat d))
            (originCube 1) (u ε) (G ε)) ∧
        (∃ m : ℝ≥0∞, 0 < m ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
          nonnegativeEssInf (originCube (1 / 2)) (u ε) = m) ∧
        ∀ (η : ℝ) (hη : 0 < η), rStarParam (d := d) q t / 2 < η →
          Tendsto (fun ε : ℝ =>
            normalizedLpMoment η hη (originCube (5 / 8)) (u ε) /
              nonnegativeEssInf (originCube (1 / 2)) (u ε))
            (𝓝[>] 0) (𝓝 ⊤) := by
  have : NeZero d := ⟨by omega⟩
  have hq0 : 0 < q := by linarith
  have hβ := whBeta_pos (d := d) hq0 ht
  have hβd := whBeta_lt _hd hp hq hs _hθ
  have hcoeff := whCoeff_weightedCoeffOn hβ hβd
  refine ⟨whField d q t, hcoeff, whUpperMoment_lt_top hβ hs hp.le hcoeff,
    whLowerMoment_pos hq ht hβ hβd hcoeff, fun ε => whu d q t ε,
    fun ε => smoothGrad (whu d q t ε), ?_, ?_, ?_⟩
  · intro ε hε hε8
    refine ⟨?_, whu_isWeightedSupersolution hβ hε⟩
    exact ae_restrict_of_forall_mem measurableSet_originCube
      (fun x hx => whu_nonneg_of_mem q t hx)
  · refine ⟨ENNReal.ofReal (whM d q t), ENNReal.ofReal_pos.2 (whM_pos _hd q t), ?_⟩
    intro ε hε hε8
    exact whEssInf _hd q t hε hε8
  · intro η hη hη'
    have hκ := whRStar_lt _hd hq ht hη'
    refine (whRatio_tendsto _hd hβ hη hκ).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with ε hε
    rw [whEssInf _hd q t hε.1 hε.2]

end

end CoarseDeGiorgi.SharpnessExamples
