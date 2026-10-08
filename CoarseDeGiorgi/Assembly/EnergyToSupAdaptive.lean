module

public import CoarseDeGiorgi.Assembly.EnergyToSupStep
public import CoarseDeGiorgi.Foundations.Iteration.AdaptiveLevels

@[expose] public section

namespace CoarseDeGiorgi.Assembly
open Filter Foundations.Iteration
open scoped Topology ENNReal

/-- Adaptive-level core driven by the exact hybrid recurrence statement. No
regularity of the abstract Q is used. -/
theorem energy_to_sup_adaptive (Q : ℝ → ℝ → ℝ≥0∞)
    {ρ R C K T μ γ g a b c ω : ℝ}
    (hρR : ρ < R) (hδ1 : R - ρ ≤ 1) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hT : 1 ≤ T) (hμ : 0 ≤ μ) (_hγ : 0 < γ) (hω : 0 < ω) (hω1 : ω < 1)
    (hratio : (2 : ℝ) ^ γ * ω = 1 / 2)
    (heb : 0 ≤ γ * (b - 2) - g) (hec : 0 ≤ γ * (c - 2) - g)
    (hcomp : μ * (b - 2) = a) (hc : 2 < c)
    (hKb : C * K ^ (2 - b) ≤ ω ^ 2 / 4)
    (hKc : C * K ^ (2 - c) ≤ ω ^ 2 / 4)
    (hfinite : Q 0 R < ⊤)
    (hmono : ∀ l k r z : ℝ, 0 ≤ l → l ≤ k → ρ ≤ r → r ≤ z → z ≤ R → Q k r ≤ Q l z)
    (hrec : ∀ l k r z : ℝ, 0 ≤ l → l < k → ρ ≤ r → r < z → z ≤ R → Q l z ≠ 0 →
      (Q k r).toReal ^ 2 ≤ (ω ^ 2 / 4) * (Q l z).toReal ^ 2 +
        C * (z - r) ^ (-g) *
          (T ^ a * (Q l z).toReal ^ b * (k - l) ^ (2 - b) +
            (Q l z).toReal ^ c * (k - l) ^ (2 - c))) :
    ∃ L : ℝ, 0 ≤ L ∧
      L ≤ 2 * K * T ^ μ * ((R - ρ) / 2) ^ (-γ) * (Q 0 R).toReal ∧ Q L ρ = 0 := by
  let δ := R - ρ
  have hδ : 0 < δ := sub_pos.mpr hρR
  let r : ℕ → ℝ := fun n => ρ + (1 / 2 : ℝ) ^ n * δ
  have hrbounds (n : ℕ) : ρ < r n ∧ r n ≤ R := by
    have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    have hp1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [r, δ]
    constructor <;> nlinarith only [hp, hp1, hρR]
  have hrgap (n : ℕ) : r n - r (n + 1) = dyadicGap δ n := by
    simp only [r, dyadicGap, pow_succ]
    ring
  have hrgap0 (n : ℕ) : r (n + 1) < r n := by
    have := dyadicGap_pos hδ n
    rw [← hrgap n] at this
    linarith only [this]
  have hgap1 (n : ℕ) : dyadicGap δ n ≤ 1 := by
    rw [← hrgap n]
    linarith only [(hrbounds n).2, (hrbounds (n + 1)).1, hδ1]
  let levels : ℕ → ℝ := Nat.rec 0 (fun n l =>
    l + K * T ^ μ * (dyadicGap δ n) ^ (-γ) * (Q l (r n)).toReal)
  have hlevel (n : ℕ) : levels (n + 1) = levels n +
      K * T ^ μ * (dyadicGap δ n) ^ (-γ) * (Q (levels n) (r n)).toReal := by rfl
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlevelmono : Monotone levels := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hlevel]
    have hg := dyadicGap_pos hδ n
    have : 0 ≤ K * T ^ μ * (dyadicGap δ n) ^ (-γ) * (Q (levels n) (r n)).toReal := by positivity
    linarith only [this]
  have hlevel0 (n : ℕ) : 0 ≤ levels n := hlevelmono (Nat.zero_le n)
  have hQfinite (n : ℕ) : Q (levels n) (r n) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite.ne
      (hmono 0 (levels n) (r n) R le_rfl (hlevel0 n) (hrbounds n).1.le
        (hrbounds n).2 le_rfl)
  let X : ℕ → ℝ := fun n => (Q (levels n) (r n)).toReal
  have hX (n : ℕ) : 0 ≤ X n := ENNReal.toReal_nonneg
  have hdecay (n : ℕ) : X (n + 1) ≤ ω * X n := by
    have hxm : X (n + 1) ≤ X n := ENNReal.toReal_mono (hQfinite n)
      (hmono (levels n) (levels (n + 1)) (r (n + 1)) (r n) (hlevel0 n)
        (hlevelmono (Nat.le_succ n)) (hrbounds (n + 1)).1.le (hrgap0 n).le (hrbounds n).2)
    by_cases hx0 : X n = 0
    · rw [hx0, mul_zero]
      exact hxm.trans_eq hx0
    have hx : 0 < X n := lt_of_le_of_ne (hX n) (Ne.symm hx0)
    have hΔ : levels (n + 1) - levels n = K * T ^ μ * (dyadicGap δ n) ^ (-γ) * X n := by
      rw [hlevel]
      dsimp [X]
      ring
    have hΔ0 : levels n < levels (n + 1) := by
      have hg := dyadicGap_pos hδ n
      have : 0 < levels (n + 1) - levels n := by rw [hΔ]; positivity
      linarith only [this]
    have hh := hrec (levels n) (levels (n + 1)) (r (n + 1)) (r n)
      (hlevel0 n) hΔ0 (hrbounds (n + 1)).1.le (hrgap0 n) (hrbounds n).2 (by
        intro hzero
        apply hx0
        simp only [X, hzero, ENNReal.toReal_zero])
    change X (n + 1) ^ 2 ≤ ω ^ 2 / 4 * X n ^ 2 + _ at hh
    rw [hrgap, hΔ] at hh
    have hb := energy_to_sup_term hC hK0 hT (dyadicGap_pos hδ n) (hgap1 n) hx heb
      (by linarith only [hcomp] : a - μ * (b - 2) ≤ 0) hKb
    have hc' := energy_to_sup_term (a := 0) hC hK0 hT (dyadicGap_pos hδ n)
      (hgap1 n) hx hec (by nlinarith only [hμ, hc] : 0 - μ * (c - 2) ≤ 0) hKc
    simp only [Real.rpow_zero, mul_one] at hc'
    rw [mul_add] at hh
    have hsq : X (n + 1) ^ 2 ≤ 3 * ω ^ 2 / 4 * X n ^ 2 := by
      nlinarith only [hh, hb, hc']
    have hp : 0 ≤ ω * X n := mul_nonneg hω.le (hX n)
    nlinarith only [hsq, hp, hX (n + 1), sq_nonneg (ω * X n)]
  obtain ⟨_, _, _, L, ht, _, hL⟩ := adaptive_levels hX hK0.le
    (Real.rpow_nonneg hT0.le μ) hδ hdecay hratio hlevel
  have hlevelsL (n : ℕ) : levels n ≤ L := hlevelmono.ge_of_tendsto ht n
  have hL0 : 0 ≤ L := hlevelsL 0
  have hQL (n : ℕ) : Q L ρ ≤ Q (levels n) (r n) := by
    exact hmono _ _ _ _ (hlevel0 n) (hlevelsL n) le_rfl (hrbounds n).1.le (hrbounds n).2
  have hQLfinite : Q L ρ ≠ ⊤ := ne_top_of_le_ne_top (hQfinite 0) (hQL (n := 0))
  have htX : Tendsto X atTop (𝓝 0) := by
    apply squeeze_zero hX (geometric_decay hω.le hdecay)
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hω.le hω1).mul_const (X 0)
  have hzero : (Q L ρ).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    exact ge_of_tendsto htX (Eventually.of_forall (fun n => ENNReal.toReal_mono (hQfinite n) (hQL (n := n))))
  refine ⟨L, hL0, ?_, ?_⟩
  · simpa only [X, levels, Nat.rec_zero, zero_add, δ, r, pow_zero, one_mul,
      show ρ + δ = R by dsimp [δ]; ring] using hL
  · exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hQLfinite

end CoarseDeGiorgi.Assembly
