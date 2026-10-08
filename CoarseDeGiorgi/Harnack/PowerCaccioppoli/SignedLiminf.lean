module

public import CoarseDeGiorgi.Statements.PowerFactor
public import Mathlib.Order.Filter.ENNReal

/-! # Liminf form of the signed-power estimate -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Filter Topology
open scoped ENNReal

/-- Pass the signed testing inequality to the lower limit of its interior
term, retaining the source factor `powerFactor m`. -/
theorem signed_surface_bound_of_liminf
    {m E B₀ : ℝ} (hm : m < 1 / 2) (hm0 : m ≠ 0)
    (_hE : 0 ≤ E) (_hB₀ : 0 ≤ B₀)
    (A B S T : ℕ → ℝ)
    (hA : Tendsto A atTop (𝓝 E))
    (hS : ENNReal.ofReal E ≤
      Filter.liminf (fun i => ENNReal.ofReal (S i)) atTop)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, |B i| ≤ B₀ + ε)
    (hSnonneg : ∀ i, 0 ≤ S i)
    (hT : ∀ i, 0 ≤ T i)
    (htest : ∀ i, m * (A i + B i) ≥ (1 - m) * (S i + T i)) :
    E ≤ CoarseDeGiorgi.powerFactor m * B₀ := by
  have hden : 0 < 1 - m := by linarith only [hm]
  have hden₂ : 0 < 1 - 2 * m := by linarith only [hm]
  have hmabs : 0 < |m| := abs_pos.mpr hm0
  have hestimate (δ : ℝ) (hδ : 0 < δ) :
      E ≤ (m * E + |m| * δ + |m| * (B₀ + δ)) / (1 - m) := by
    let C : ℝ := (m * E + |m| * δ + |m| * (B₀ + δ)) / (1 - m)
    have hclose : ∀ᶠ i in atTop, |A i - E| < δ := by
      filter_upwards [hA.eventually (Metric.ball_mem_nhds E hδ)] with i hi
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hi
    have hMA (i : ℕ) (hi : |A i - E| < δ) :
        m * A i ≤ m * E + |m| * δ := by
      have hdiff : m * (A i - E) ≤ |m| * δ := by
        calc
          m * (A i - E) ≤ |m * (A i - E)| := le_abs_self _
          _ = |m| * |A i - E| := abs_mul _ _
          _ ≤ |m| * δ := mul_le_mul_of_nonneg_left hi.le (abs_nonneg m)
      calc
        m * A i = m * E + m * (A i - E) := by ring
        _ ≤ m * E + |m| * δ := by nlinarith only [hdiff]
    have hBδ : ∀ᶠ i in atTop, |B i| ≤ B₀ + δ := hB δ hδ
    have hMB (i : ℕ) (hi : |B i| ≤ B₀ + δ) :
        m * B i ≤ |m| * (B₀ + δ) := by
      calc
        m * B i ≤ |m * B i| := le_abs_self _
        _ = |m| * |B i| := abs_mul _ _
        _ ≤ |m| * (B₀ + δ) := mul_le_mul_of_nonneg_left hi (abs_nonneg m)
    have hSc (i : ℕ) (hi : |B i| ≤ B₀ + δ) :
        (1 - m) * S i ≤ m * A i + |m| * (B₀ + δ) := by
      calc
        (1 - m) * S i ≤ (1 - m) * (S i + T i) := by
          nlinarith [mul_nonneg hden.le (hT i)]
        _ ≤ m * (A i + B i) := htest i
        _ = m * A i + m * B i := by ring
        _ ≤ m * A i + |m| * (B₀ + δ) := by nlinarith only [hMB i hi]
    have hbound : ∀ᶠ i in atTop, S i ≤ C := by
      filter_upwards [hclose, hBδ] with i hiA hiB
      dsimp [C]
      apply (le_div_iff₀ hden).2
      calc
        S i * (1 - m) ≤ m * A i + |m| * (B₀ + δ) := by
          nlinarith [hSc i hiB]
        _ ≤ m * E + |m| * δ + |m| * (B₀ + δ) := by
          nlinarith [hMA i hiA]
    have hC : 0 ≤ C := by
      rcases (hbound.and (Eventually.of_forall hSnonneg)).exists with ⟨i, hi, hiS⟩
      exact hiS.trans hi
    have hboundENN : ∀ᶠ i in atTop, ENNReal.ofReal (S i) ≤ ENNReal.ofReal C := by
      filter_upwards [hbound] with i hi
      exact ENNReal.ofReal_le_ofReal hi
    have hlim : Filter.liminf (fun i => ENNReal.ofReal (S i)) atTop ≤
        ENNReal.ofReal C := by
      calc
        Filter.liminf (fun i => ENNReal.ofReal (S i)) atTop ≤
            Filter.liminf (fun _ : ℕ => ENNReal.ofReal C) atTop :=
          Filter.liminf_le_liminf hboundENN
        _ = ENNReal.ofReal C := by simp
    have hEC : E ≤ C := by
      have hreal : ENNReal.ofReal E ≤ ENNReal.ofReal C := hS.trans hlim
      exact (ENNReal.ofReal_le_ofReal_iff hC).mp hreal
    simpa only [C] using hEC
  by_contra hgoal
  have htarget : CoarseDeGiorgi.powerFactor m * B₀ < E := lt_of_not_ge hgoal
  have hscaled : |m| * B₀ < (1 - 2 * m) * E := by
    have hdiv : (|m| * B₀) / (1 - 2 * m) < E := by
      simpa [CoarseDeGiorgi.powerFactor, div_mul_eq_mul_div] using htarget
    have hscaled' := (div_lt_iff₀ hden₂).mp hdiv
    nlinarith only [hscaled']
  let δ : ℝ := ((1 - 2 * m) * E - |m| * B₀) / (4 * |m|)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (sub_pos.mpr hscaled) (mul_pos (by norm_num) hmabs)
  have hδeq : 2 * |m| * δ = ((1 - 2 * m) * E - |m| * B₀) / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hmabs]
    ring
  have hbound := hestimate δ hδ
  have hmul : E * (1 - m) ≤ m * E + |m| * δ + |m| * (B₀ + δ) :=
    (le_div_iff₀ hden).mp hbound
  nlinarith [hscaled, hδeq]

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
