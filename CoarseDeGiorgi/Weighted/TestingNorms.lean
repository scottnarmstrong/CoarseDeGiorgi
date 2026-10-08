import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.MeanInequalities
import CoarseDeGiorgi.Foundations.Iteration.HoleFilling

namespace CoarseDeGiorgi.Weighted

open MeasureTheory Filter
open scoped ENNReal

/-- Interpolation of a test function between its essential supremum and Lʳ norm. -/
theorem testing_l2_interpolation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 2) :
    eLpNorm f 2 μ ≤ eLpNorm f ⊤ μ ^ (1 - r / 2) *
      eLpNorm f (ENNReal.ofReal r) μ ^ (r / 2) := by
  have hw : 0 < 1 - r / 2 := by linarith only [hr2]
  have hz : 0 < r / 2 := half_pos hr
  let g : α → ℝ := fun x => ‖f x‖ ^ (1 - r / 2)
  let h : α → ℝ := fun x => ‖f x‖ ^ (r / 2)
  have hprod : (fun x => g x * h x) = fun x => ‖f x‖ := by
    funext x
    dsimp only [g, h]
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) hw.le hz.le,
      sub_add_cancel, Real.rpow_one]
  have hn := eLpNorm_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μ) (f := g) (g := h)
    2 (fun a b : ℝ => a * b) 1 continuous_mul
    (Eventually.of_forall fun x => by simp only [nnnorm_mul, one_mul]; rfl)
    (by norm_num)
  rw [hprod, eLpNorm_norm f hf] at hn
  dsimp only [g, h] at hn
  rw [eLpNorm_norm_rpow f hf hw, eLpNorm_norm_rpow f hf hz] at hn
  have hexp : (2 : ENNReal) * ENNReal.ofReal (r / 2) = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  simpa only [ENNReal.coe_one, one_mul, ENNReal.top_mul', ENNReal.ofReal_eq_zero,
    not_le.mpr hw, ite_false, hexp] using hn

/-- Young absorption with the exponents needed for the Lʳ local bound. -/
theorem testing_young {A M N : ENNReal} {z ε : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (hε : 0 < ε) :
    A * M ^ (1 - z) * N ^ z ≤ ENNReal.ofReal ε * M +
      (ENNReal.ofReal ε) ^ (-(1 - z) / z) * A ^ (1 / z) * N := by
  have hw : 0 < 1 - z := sub_pos.mpr hz1
  have hconj : (1 / (1 - z)).HolderConjugate (1 / z) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (lt_div_iff₀ hw).mpr (by linarith only [hz])
    · simp only [one_div, inv_inv, sub_add_cancel]
  let e := ENNReal.ofReal ε
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have het : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : e ^ (1 - z) * e ^ (-(1 - z)) = 1 := by
    rw [← ENNReal.rpow_add _ _ he0 het]
    simp only [add_neg_cancel, ENNReal.rpow_zero]
  have ha : (e ^ (1 - z) * M ^ (1 - z)) ^ (1 / (1 - z)) = e * M := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hw).le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hw.ne',
      ENNReal.rpow_one, ENNReal.rpow_one]
  have hb : (e ^ (-(1 - z)) * A * N ^ z) ^ (1 / z) =
      e ^ (-(1 - z) / z) * A ^ (1 / z) * N := by
    simp only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hz).le,
      ← ENNReal.rpow_mul]
    rw [mul_one_div_cancel hz.ne', ENNReal.rpow_one]
    rw [show -(1 - z) * (1 / z) = -(1 - z) / z by ring]
  have hy := ENNReal.young_inequality
    (e ^ (1 - z) * M ^ (1 - z)) (e ^ (-(1 - z)) * A * N ^ z) hconj
  have hleft : (e ^ (1 - z) * M ^ (1 - z)) * (e ^ (-(1 - z)) * A * N ^ z) =
      A * M ^ (1 - z) * N ^ z := by
    calc
      _ = (e ^ (1 - z) * e ^ (-(1 - z))) * (A * M ^ (1 - z) * N ^ z) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [hleft, ha, hb] at hy
  apply hy.trans
  apply add_le_add
  · rw [div_eq_mul_inv]
    simpa only [mul_one] using mul_le_mul' (le_refl (e * M))
      (ENNReal.inv_le_one.mpr (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hconj.lt.le))
  · rw [div_eq_mul_inv]
    simpa only [mul_one] using mul_le_mul' (le_refl (e ^ (-(1 - z) / z) * A ^ (1 / z) * N))
      (ENNReal.inv_le_one.mpr (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hconj.symm.lt.le))

/-- Hole filling upgrades an L² local estimate to its Lʳ estimate.
All the hypotheses concern the same function and nested measures. -/
theorem testing_lr_bound_of_l2 {α : Type*} [MeasurableSpace α]
    {μ : ℝ → Measure α} (hμ : Monotone μ)
    {C : ENNReal} (hC : C < ⊤) {γ r : ℝ} (hγ : 0 < γ)
    (hr : 0 < r) (hr2 : r < 2) :
    ∃ K : ENNReal, K < ⊤ ∧ ∀ (f : α → ℝ) (B : ENNReal) (b : ℝ), 0 < B → B < ⊤ →
      ∀ ρ R : ℝ, ρ < R → eLpNorm f ⊤ (μ R) < ⊤ →
      eLpNorm f (ENNReal.ofReal r) (μ R) < ⊤ →
      AEStronglyMeasurable f (μ R) →
      (∀ ρ' R' : ℝ, ρ ≤ ρ' → ρ' < R' → R' ≤ R →
        eLpNorm f ⊤ (μ ρ') ≤ C * (ENNReal.ofReal (R' - ρ')) ^ (-γ) *
          B ^ b * eLpNorm f 2 (μ R')) →
      eLpNorm f ⊤ (μ ρ) ≤ K * (ENNReal.ofReal (R - ρ)) ^ (-2 * γ / r) *
        B ^ (2 * b / r) * eLpNorm f (ENNReal.ofReal r) (μ R) := by
  let z := r / 2
  let k := γ / z
  let ε := 1 / (4 * (2 : ℝ) ^ k)
  let η := 2 * ε
  have hz : 0 < z := half_pos hr
  have hz1 : z < 1 := by dsimp only [z]; linarith only [hr2]
  have hk : 0 < k := div_pos hγ hz
  have hε : 0 < ε := one_div_pos.mpr (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
  have hη : 0 < η := mul_pos (by norm_num) hε
  have hsmall : (2 * ε) * (2 : ℝ) ^ k < 1 := by
    dsimp only [ε]
    have hpow : (2 : ℝ) ^ k ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp
    norm_num
  let J := (ENNReal.ofReal η) ^ (-(1 - z) / z) * C ^ (1 / z)
  have hJ : J < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hη).ne' ENNReal.ofReal_ne_top).lt_top
    (ENNReal.rpow_lt_top_of_nonneg (one_div_pos.mpr hz).le hC.ne)
  let K := ENNReal.ofReal (Foundations.Iteration.holeFillingConstant ε k) * J
  refine ⟨K, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ, ?_⟩
  intro f B b hB hBt ρ R hρR hM hN hf hbound
  let N := eLpNorm f (ENNReal.ofReal r) (μ R)
  let A := J * B ^ (b / z) * N
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hJ.ne (ENNReal.rpow_ne_top_of_ne_zero hB.ne' hBt.ne)) hN.ne
  have hstep : ∀ ρ' R' : ℝ, ρ ≤ ρ' → ρ' < R' → R' ≤ R →
      eLpNorm f ⊤ (μ ρ') ≤ ENNReal.ofReal (2 * ε) * eLpNorm f ⊤ (μ R') +
        ENNReal.ofReal (A.toReal * (R' - ρ') ^ (-k)) := by
    intro ρ' R' hρ' hgap hR'
    have hf' := hf.mono_measure (hμ hR')
    have hi := testing_l2_interpolation hf' hr hr2
    have hn := eLpNorm_mono_measure f (hμ hR') (p := ENNReal.ofReal r)
    have hi' : eLpNorm f 2 (μ R') ≤ eLpNorm f ⊤ (μ R') ^ (1 - z) * N ^ z :=
      hi.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hn hz.le))
    have hy := testing_young (A := C * (ENNReal.ofReal (R' - ρ')) ^ (-γ) * B ^ b)
      (M := eLpNorm f ⊤ (μ R')) (N := N) hz hz1 hη
    have hpower : (C * (ENNReal.ofReal (R' - ρ')) ^ (-γ) * B ^ b) ^ (1 / z) =
        C ^ (1 / z) * (ENNReal.ofReal (R' - ρ')) ^ (-k) * B ^ (b / z) := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hz).le,
        ← ENNReal.rpow_mul]
      rw [show -γ * (1 / z) = -k by dsimp only [k]; ring,
        show b * (1 / z) = b / z by ring]
    have h := (hbound ρ' R' hρ' hgap hR').trans (mul_le_mul' le_rfl hi')
    rw [← mul_assoc] at h
    have h' := h.trans hy
    rw [hpower] at h'
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hA,
      ← ENNReal.ofReal_rpow_of_pos (sub_pos.mpr hgap)]
    convert h' using 1
    dsimp only [A, J, η]
    ring
  have hh := Foundations.Iteration.hole_filling_of_all_pairs
    (fun S T hST => eLpNorm_mono_measure f (hμ hST) (p := ⊤)) hρR hε.le
    ENNReal.toReal_nonneg hk.le hsmall hM hstep
  rw [ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_rpow_of_pos (sub_pos.mpr hρR)] at hh
  have hk' : -k = -2 * γ / r := by dsimp only [k, z]; ring
  have hb' : b / z = 2 * b / r := by dsimp only [z]; ring
  rw [hk'] at hh
  dsimp only [A] at hh
  rw [hb'] at hh
  convert hh using 1
  dsimp only [K]
  ring

end CoarseDeGiorgi.Weighted
