module

public import CoarseDeGiorgi.Weighted.Truncation.Chain
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Powers

open Filter Set Topology
open scoped NNReal

private noncomputable def powerFloor (ε x : ℝ) : ℝ :=
  x * (1 - Real.smoothTransition (-x / (ε / 2)))

private lemma powerFloor_eq_self {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    powerFloor ε x = x := by
  have harg : -x / (ε / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) (half_pos hε).le
  simp [powerFloor, Real.smoothTransition.zero_of_nonpos harg]

private lemma powerFloor_eq_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ -ε / 2) :
    powerFloor ε x = 0 := by
  have harg : 1 ≤ -x / (ε / 2) := by
    apply (le_div_iff₀ (half_pos hε)).2
    linarith
  simp [powerFloor, Real.smoothTransition.one_of_one_le harg]

private lemma powerFloor_lower {ε x : ℝ} (hε : 0 < ε) :
    -ε / 2 ≤ powerFloor ε x := by
  by_cases hx : 0 ≤ x
  · rw [powerFloor_eq_self hε hx]
    linarith
  · have hxneg : x < 0 := lt_of_not_ge hx
    by_cases hc : x ≤ -ε / 2
    · rw [powerFloor_eq_zero hε hc]
      linarith
    · have hxlo : -ε / 2 < x := lt_of_not_ge hc
      let s := Real.smoothTransition (-x / (ε / 2))
      have hs0 : 0 ≤ s := Real.smoothTransition.nonneg _
      have hs1 : s ≤ 1 := Real.smoothTransition.le_one _
      have hprod : 0 ≤ x * (-s) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hxneg) (by linarith)
      have hmul : x ≤ x * (1 - s) := by
        calc
          x ≤ x + x * (-s) := by linarith
          _ = x * (1 - s) := by ring
      change -ε / 2 ≤ x * (1 - s)
      dsimp [s] at hmul ⊢
      linarith

private noncomputable def shiftedPowerExtension (ε q x : ℝ) : ℝ :=
  (powerFloor ε x + ε) ^ q

private lemma shiftedPowerExtension_contDiff {ε q : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (shiftedPowerExtension ε q) := by
  have hfloor : ContDiff ℝ (⊤ : ℕ∞) (powerFloor ε) := by
    unfold powerFloor
    fun_prop (disch := positivity)
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun x => powerFloor ε x + ε) :=
    hfloor.add contDiff_const
  apply hbase.rpow_const_of_ne
  intro x
  exact (ne_of_gt (by linarith [powerFloor_lower hε (x := x)]))

private lemma shiftedPowerExtension_eq_rpow {ε q x : ℝ} (hε : 0 < ε)
    (hx : 0 ≤ x) : shiftedPowerExtension ε q x = (x + ε) ^ q := by
  rw [shiftedPowerExtension, powerFloor_eq_self hε hx]

private lemma shiftedPowerExtension_eq_const {ε q x : ℝ} (hε : 0 < ε)
    (hx : x < -ε / 2) : shiftedPowerExtension ε q x = ε ^ q := by
  rw [shiftedPowerExtension, powerFloor_eq_zero hε (le_of_lt hx), zero_add]

private lemma shiftedPowerExtension_eq_positive {ε q x : ℝ} (hε : 0 < ε)
    (hx : 0 < x) :
    deriv (shiftedPowerExtension ε q) x = q * (x + ε) ^ (q - 1) := by
  have heq : shiftedPowerExtension ε q =ᶠ[𝓝 x] (fun y => (y + ε) ^ q) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact shiftedPowerExtension_eq_rpow hε hy.le
  have hderiv : HasDerivAt (fun y => (y + ε) ^ q) (q * (x + ε) ^ (q - 1)) x := by
    have hbase : x + ε ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hx hε.le)
    have hcomp :=
      (Real.hasDerivAt_rpow_const (x := x + ε) (p := q) (Or.inl hbase)).comp x
        ((hasDerivAt_id x).add_const ε)
    change HasDerivAt (fun y => (y + ε) ^ q) (q * (x + ε) ^ (q - 1) * 1) x at hcomp
    simpa only [mul_one] using hcomp
  exact (hderiv.congr_of_eventuallyEq heq).deriv

private lemma shiftedPowerExtension_deriv_zero {ε q x : ℝ} (hε : 0 < ε)
    (hx : x < -ε / 2) : deriv (shiftedPowerExtension ε q) x = 0 := by
  have heq : shiftedPowerExtension ε q =ᶠ[𝓝 x] fun _ => ε ^ q := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact shiftedPowerExtension_eq_const hε hy
  exact (hasDerivAt_const x (ε ^ q)).congr_of_eventuallyEq heq |>.deriv

/-- Smooth bounded-derivative extensions of a shifted power on the nonnegative half-line.
The extension agrees with `(x + ε)^q` for `x ≥ 0`, and applies for every `q < 1`.
-/
theorem exists_smooth_shifted_rpow_extension (ε q : ℝ) (hε : 0 < ε) (hq : q < 1) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      (∀ x, 0 ≤ x → Φ x = (x + ε) ^ q) ∧
      (∀ x, 0 ≤ x → deriv Φ x = q * (x + ε) ^ (q - 1)) ∧
      ∃ L : ℝ≥0, ∀ x, |deriv Φ x| ≤ L := by
  let Φ := shiftedPowerExtension ε q
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := shiftedPowerExtension_contDiff hε
  have hderivCont : Continuous (deriv Φ) := hΦ.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hderivCont.norm.continuousOn
    (K := Set.Icc (-ε / 2) 0)
  let M : ℝ := |q| * ε ^ (q - 1)
  let B : ℝ := max (max C 0) M
  have hB0 : 0 ≤ B := le_trans (le_max_right C 0) (le_max_left (max C 0) M)
  let L : ℝ≥0 := ⟨B, hB0⟩
  refine ⟨Φ, hΦ, ?_, ?_, L, ?_⟩
  · intro x hx
    exact shiftedPowerExtension_eq_rpow hε hx
  · intro x hx
    by_cases hxp : 0 < x
    · exact shiftedPowerExtension_eq_positive hε hxp
    · have hx0 : x = 0 := le_antisymm (le_of_not_gt hxp) hx
      subst x
      have hpow : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (x + ε) ^ (q - 1)) 0 :=
        (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne
          (ne_of_gt (by simpa using hε))
      have hcontR : ContinuousAt (fun x : ℝ => q * (x + ε) ^ (q - 1)) 0 :=
        (contDiffAt_const.mul hpow).continuousAt
      have htL : Tendsto (deriv Φ) (𝓝[>] (0 : ℝ)) (𝓝 (deriv Φ 0)) :=
        hderivCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have htR : Tendsto (fun x : ℝ => q * (x + ε) ^ (q - 1))
          (𝓝[>] (0 : ℝ)) (𝓝 (q * ε ^ (q - 1))) := by
        simpa only [zero_add] using hcontR.tendsto.mono_left nhdsWithin_le_nhds
      have heq : (fun x : ℝ => deriv Φ x) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun x => q * (x + ε) ^ (q - 1)) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact shiftedPowerExtension_eq_positive hε hx
      have htr := htR.congr' heq.symm
      have heq0 := tendsto_nhds_unique htL htr
      simpa only [zero_add] using heq0
  · intro x
    by_cases hxneg : x < -ε / 2
    · rw [shiftedPowerExtension_deriv_zero hε hxneg, abs_zero]
      exact hB0
    · by_cases hxpos : 0 < x
      · rw [shiftedPowerExtension_eq_positive hε hxpos, abs_mul]
        have hq1 : q - 1 ≤ 0 := by linarith
        have hpow : (x + ε) ^ (q - 1) ≤ ε ^ (q - 1) :=
          Real.rpow_le_rpow_of_nonpos hε (le_add_of_nonneg_left hxpos.le) hq1
        have hpowpos : 0 < (x + ε) ^ (q - 1) :=
          Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg hxpos hε.le) _
        rw [abs_of_pos hpowpos]
        change |q| * (x + ε) ^ (q - 1) ≤ B
        exact (mul_le_mul_of_nonneg_left hpow (abs_nonneg q)).trans
          (le_max_right (max C 0) M)
      · have hxle : x ≤ 0 := le_of_not_gt hxpos
        have hxin : x ∈ Set.Icc (-ε / 2) 0 := ⟨le_of_not_gt hxneg, hxle⟩
        have hbound := hC ⟨x, hxin, rfl⟩
        have hnorm : |deriv Φ x| ≤ C := by simpa only [Real.norm_eq_abs] using hbound
        exact hnorm.trans (le_trans (le_max_left C 0) (le_max_left (max C 0) M))

end CoarseDeGiorgi.Harnack.Powers
