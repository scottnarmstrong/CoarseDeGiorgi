module

public import CoarseDeGiorgi.Assembly.EnergyToSupParameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace CoarseDeGiorgi.Assembly
open Filter
open scoped Topology

/-- Both negative powers can be made uniformly small by one parameter-only K. -/
theorem energy_to_sup_choose_K {C ε b c : ℝ} (hε : 0 < ε) (hb : 2 < b) (hc : 2 < c) :
    ∃ K : ℝ, 1 ≤ K ∧ C * K ^ (2 - b) ≤ ε ∧ C * K ^ (2 - c) ≤ ε := by
  have hb0 : 0 < b - 2 := by linarith
  have hc0 : 0 < c - 2 := by linarith
  have htb : Tendsto (fun K : ℝ => C * K ^ (2 - b)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using (tendsto_rpow_neg_atTop hb0).const_mul C
  have htc : Tendsto (fun K : ℝ => C * K ^ (2 - c)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using (tendsto_rpow_neg_atTop hc0).const_mul C
  obtain ⟨Z, hsmall⟩ := eventually_atTop.mp ((htb.eventually (gt_mem_nhds hε)).and
    (htc.eventually (gt_mem_nhds hε)))
  exact ⟨max 1 Z, le_max_left _ _, (hsmall _ (le_max_right _ _)).1.le,
    (hsmall _ (le_max_right _ _)).2.le⟩

/-- Factor one nonlinear term after the adaptive level increment. -/
theorem energy_to_sup_term {C K T δ X μ γ g b a ε : ℝ}
    (hC : 0 ≤ C) (hK : 0 < K) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hX : 0 < X) (he : 0 ≤ γ * (b - 2) - g) (hcomp : a - μ * (b - 2) ≤ 0)
    (hsmall : C * K ^ (2 - b) ≤ ε) :
    C * δ ^ (-g) * T ^ a * X ^ b *
      (K * T ^ μ * δ ^ (-γ) * X) ^ (2 - b) ≤ ε * X ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hid : C * δ ^ (-g) * T ^ a * X ^ b *
      (K * T ^ μ * δ ^ (-γ) * X) ^ (2 - b) =
      (C * K ^ (2 - b)) * δ ^ (γ * (b - 2) - g) *
        T ^ (a - μ * (b - 2)) * X ^ 2 := by
    rw [Real.mul_rpow (by positivity) hX.le,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hδ.le _),
      Real.mul_rpow hK.le (Real.rpow_nonneg hT0.le _),
      ← Real.rpow_mul hT0.le, ← Real.rpow_mul hδ.le]
    calc
      _ = (C * K ^ (2 - b)) * (δ ^ (-g) * δ ^ (-γ * (2 - b))) *
          (T ^ a * T ^ (μ * (2 - b))) * (X ^ b * X ^ (2 - b)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hT0, ← Real.rpow_add hX]
        rw [show -g + -γ * (2 - b) = γ * (b - 2) - g by ring,
          show a + μ * (2 - b) = a - μ * (b - 2) by ring,
          show b + (2 - b) = (2 : ℝ) by ring, Real.rpow_two]
  rw [hid]
  have hdle : δ ^ (γ * (b - 2) - g) ≤ 1 := Real.rpow_le_one hδ.le hδ1 he
  have htle : T ^ (a - μ * (b - 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT hcomp
  calc
    _ ≤ (C * K ^ (2 - b)) * 1 * 1 * X ^ 2 := by gcongr
    _ ≤ ε * X ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_right hsmall (sq_nonneg X)

end CoarseDeGiorgi.Assembly
