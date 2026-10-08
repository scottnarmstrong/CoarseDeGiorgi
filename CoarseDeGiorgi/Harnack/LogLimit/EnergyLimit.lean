module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import CoarseDeGiorgi.Weighted.Energy
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.PowerFactor
public import Homogenization.Ambient.CoefficientField

@[expose] public section

namespace CoarseDeGiorgi.Harnack.LogLimit

open Homogenization MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

private theorem positiveClipRpow_continuous (ε p : ℝ) (hε : 0 < ε) :
    Continuous (fun x : ℝ => (max x ε) ^ p) := by
  have hmax : Continuous (fun x : ℝ => max x ε) :=
    by fun_prop
  apply hmax.rpow_const
  intro x
  exact Or.inl (ne_of_gt (lt_of_lt_of_le hε (le_max_right x ε)))

private theorem negativePower_bound {ε x z L : ℝ} (hε : 0 < ε)
    (hx : ε ≤ x) (hzlo : -L ≤ z) (hzhi : z ≤ 0) :
    |x ^ z| ≤ 1 + ε ^ (-L) := by
  have hxpos : 0 < x := lt_of_lt_of_le hε hx
  rw [abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  by_cases hxone : 1 ≤ x
  · calc
      x ^ z ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hxone hzhi
      _ ≤ 1 + ε ^ (-L) := by nlinarith [Real.rpow_nonneg hε.le (-L)]
  · have hxlt : x ≤ 1 := le_of_not_ge hxone
    have hepsone : ε ≤ 1 := le_trans hx hxlt
    have hbase : x ^ z ≤ ε ^ z := Real.rpow_le_rpow_of_nonpos hε hx hzhi
    have hexp : ε ^ z ≤ ε ^ (-L) :=
      Real.rpow_le_rpow_of_exponent_ge hε hepsone hzlo
    calc
      x ^ z ≤ ε ^ z := hbase
      _ ≤ ε ^ (-L) := hexp
      _ ≤ 1 + ε ^ (-L) := by nlinarith [Real.rpow_nonneg hε.le (-L)]

/-- On a probability space, the shifted negative powers have Lʳ norm tending
to the norm of the constant one. This is the source limit for
`‖(u+ε)^m‖_{Lʳ}`. -/
theorem tendsto_eLpNorm_shifted_negative_power_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 < ε) (U : α → ℝ)
    (hU : AEStronglyMeasurable U μ)
    (hUlower : ∀ᵐ x ∂μ, ε ≤ U x)
    (r : ℝ) (hr : 0 < r)
    (m : ℕ → ℝ)
    (hmlo : ∀ n, -1 ≤ m n)
    (hmhi : ∀ n, m n ≤ 0)
    (hmtendsto : Tendsto m atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal r) μ)
      atTop (𝓝 1) := by
  let Uε : α → ℝ := fun x => max (U x) ε
  let V : ℕ → α → ℝ := fun n x => Uε x ^ (m n)
  let I : ℕ → α → ℝ := fun n x => Uε x ^ (m n * r)
  have hUε : AEStronglyMeasurable Uε μ := by
    have hc : Continuous (fun x : ℝ => max x ε) := by fun_prop
    exact hc.comp_aestronglyMeasurable hU
  have hVmeas (n : ℕ) : AEStronglyMeasurable (V n) μ := by
    dsimp [V, Uε]
    exact (positiveClipRpow_continuous ε (m n) hε).comp_aestronglyMeasurable hU
  have hImeas (n : ℕ) : AEStronglyMeasurable (I n) μ := by
    dsimp [I, Uε]
    exact (positiveClipRpow_continuous ε (m n * r) hε).comp_aestronglyMeasurable hU
  have hVbound (n : ℕ) : ∀ᵐ x ∂μ, ‖V n x‖ ≤ 1 + ε ^ (-1 : ℝ) := by
    filter_upwards with x
    have hbase : ε ≤ Uε x := le_max_right _ _
    have hzlo : -1 ≤ m n := hmlo n
    have hzhi : m n ≤ 0 := hmhi n
    simpa [V, Real.norm_eq_abs] using
      negativePower_bound (L := 1) hε hbase hzlo hzhi
  have hVmem (n : ℕ) : MemLp (V n) (ENNReal.ofReal r) μ :=
    MemLp.of_bound (hVmeas n) (1 + ε ^ (-1 : ℝ)) (hVbound n)
  have hIbound (n : ℕ) : ∀ᵐ x ∂μ, ‖I n x‖ ≤ 1 + ε ^ (-r) := by
    filter_upwards with x
    have hbase : ε ≤ Uε x := le_max_right _ _
    have hzlo : -r ≤ m n * r := by
      nlinarith [mul_le_mul_of_nonneg_right (hmlo n) hr.le]
    have hzhi : m n * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hmhi n) hr.le
    simpa [I, Real.norm_eq_abs] using
      negativePower_bound (L := r) hε hbase hzlo hzhi
  have hExp : Tendsto (fun n => m n * r) atTop (𝓝 0) := by
    simpa [mul_comm] using hmtendsto.const_mul r
  have hIpoint : ∀ᵐ x ∂μ, Tendsto (fun n => I n x) atTop (𝓝 1) := by
    filter_upwards with x
    have hpos : 0 < Uε x := lt_of_lt_of_le hε (le_max_right _ _)
    have hpow : Tendsto (fun n => Uε x ^ (m n * r)) atTop
        (𝓝 (Uε x ^ (0 : ℝ))) := by
      exact ((Real.continuous_const_rpow (ne_of_gt hpos)).continuousAt).tendsto.comp hExp
    simpa [I] using hpow
  have hIint : Tendsto (fun n => ∫ x, I n x ∂μ) atTop (𝓝 1) := by
    have hDCT := tendsto_integral_of_dominated_convergence
      (fun _ : α => 1 + ε ^ (-r)) hImeas (integrable_const _)
      hIbound hIpoint
    simpa [measure_univ] using hDCT
  have hroot : Tendsto
      (fun n => (∫ x, I n x ∂μ) ^ (1 / r)) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => x ^ (1 / r)) 1 :=
      Real.continuousAt_rpow_const 1 (1 / r) (Or.inl one_ne_zero)
    convert hc.tendsto.comp hIint using 1
    · rfl
    · norm_num
  have hrootENN : Tendsto
      (fun n => ENNReal.ofReal ((∫ x, I n x ∂μ) ^ (1 / r)))
      atTop (𝓝 1) := by
    convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp hroot using 1
    · rfl
    · norm_num
  have hVae (n : ℕ) : (fun x => U x ^ (m n)) =ᵐ[μ] V n := by
    filter_upwards [hUlower] with x hx
    simp [V, Uε, max_eq_left hx]
  have hpowIntegral (n : ℕ) :
      ∫ x, ‖V n x‖ ^ r ∂μ = ∫ x, I n x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    have hpos : 0 < Uε x := lt_of_lt_of_le hε (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    rw [← Real.rpow_mul hpos.le]
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hpTop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hformula (n : ℕ) :
      eLpNorm (V n) (ENNReal.ofReal r) μ =
        ENNReal.ofReal ((∫ x, ‖V n x‖ ^ r ∂μ) ^ (1 / r)) := by
    simpa [ENNReal.toReal_ofReal hr.le] using
      (hVmem n).eLpNorm_eq_integral_rpow_norm hp0 hpTop
  have hseq :
      (fun n => eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal r) μ) =
      (fun n => ENNReal.ofReal ((∫ x, I n x ∂μ) ^ (1 / r))) := by
    funext n
    rw [eLpNorm_congr_ae (hVae n), hformula n, hpowIntegral n]
  rw [hseq]
  exact hrootENN

/-- The weighted energy of the divided power gradients converges to the
logarithmic gradient energy. This is the weighted-energy form of the preceding
source density limit. -/
theorem tendsto_weightedEnergy_shifted_negative_power
    {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (ha : IsWeightedCoeffOn V a)
    (U : Vec d → ℝ) (G : Vec d → Vec d)
    (ε : ℝ) (hε : 0 < ε)
    (hU : AEStronglyMeasurable U (volume.restrict V))
    (hUlower : ∀ᵐ x ∂(volume.restrict V), ε ≤ U x)
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hGenergy : weightedEnergy a V G < ⊤)
    (m : ℕ → ℝ)
    (hmlo : ∀ n, -1 ≤ m n)
    (hmhi : ∀ n, m n ≤ 0)
    (hmtendsto : Tendsto m atTop (𝓝 0)) :
    Tendsto
      (fun n => weightedEnergy a V
        (fun x => U x ^ (m n - 1) • G x))
      atTop (𝓝 (weightedEnergy a V (fun x => U x ^ (-1 : ℝ) • G x))) := by
  let μ : Measure (Vec d) := volume.restrict V
  let q : Vec d → ℝ := fun x => vecDot (G x) (matVecMul (a x) (G x))
  let Uε : Vec d → ℝ := fun x => max (U x) ε
  let I : ℕ → Vec d → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (Uε x ^ (2 * m n - 2) * q x)
  have hqmeas : AEStronglyMeasurable q μ := by
    dsimp [q, μ]
    exact Weighted.quadratic_aestronglyMeasurable ha hG
  have hqnonneg : 0 ≤ᵐ[μ] q := by
    dsimp [q, μ]
    exact Weighted.quadratic_nonneg ha G
  have hUε : AEStronglyMeasurable Uε μ := by
    have hc : Continuous (fun x : ℝ => max x ε) := by fun_prop
    exact hc.comp_aestronglyMeasurable hU
  have hImeas (n : ℕ) : AEMeasurable (I n) μ := by
    have hpow : AEStronglyMeasurable (fun x => Uε x ^ (2 * m n - 2)) μ := by
      exact (positiveClipRpow_continuous ε (2 * m n - 2) hε).comp_aestronglyMeasurable hU
    dsimp [I]
    exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      (hpow.mul hqmeas)).aemeasurable
  have hK : 0 ≤ 1 + ε ^ (-4 : ℝ) := by positivity
  have hdom (n : ℕ) : ∀ᵐ x ∂μ,
      I n x ≤ ENNReal.ofReal (1 + ε ^ (-4 : ℝ)) * ENNReal.ofReal (q x) := by
    filter_upwards [hqnonneg] with x hqx
    have hbase : ε ≤ Uε x := le_max_right _ _
    have hzlo : -4 ≤ 2 * m n - 2 := by nlinarith [hmlo n]
    have hzhi : 2 * m n - 2 ≤ 0 := by nlinarith [hmhi n]
    have hpow := negativePower_bound (L := 4) hε hbase hzlo hzhi
    have hscalar : Uε x ^ (2 * m n - 2) ≤ 1 + ε ^ (-4 : ℝ) := by
      exact (le_abs_self _).trans hpow
    have hprod := mul_le_mul_of_nonneg_right hscalar hqx
    calc
      ENNReal.ofReal (Uε x ^ (2 * m n - 2) * q x) ≤
          ENNReal.ofReal ((1 + ε ^ (-4 : ℝ)) * q x) :=
        ENNReal.ofReal_le_ofReal hprod
      _ = ENNReal.ofReal (1 + ε ^ (-4 : ℝ)) * ENNReal.ofReal (q x) :=
        by rw [← ENNReal.ofReal_mul hK]
  have hboundFinite :
      (∫⁻ x, ENNReal.ofReal (1 + ε ^ (-4 : ℝ)) * ENNReal.ofReal (q x) ∂μ) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    change ENNReal.ofReal (1 + ε ^ (-4 : ℝ)) * weightedEnergy a V G ≠ ⊤
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGenergy.ne
  have hexp : Tendsto (fun n => 2 * m n - 2) atTop (𝓝 (-2 : ℝ)) := by
    convert (tendsto_const_nhds.mul hmtendsto).sub tendsto_const_nhds using 1
    norm_num
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => I n x) atTop
      (𝓝 (ENNReal.ofReal (U x ^ (-2 : ℝ) * q x))) := by
    filter_upwards [hUlower] with x hUx
    have hUxpos : 0 < U x := lt_of_lt_of_le hε hUx
    have hpow : Tendsto (fun n => U x ^ (2 * m n - 2)) atTop
        (𝓝 (U x ^ (-2 : ℝ))) := by
      exact ((Real.continuous_const_rpow (ne_of_gt hUxpos)).continuousAt).tendsto.comp hexp
    have hreal : Tendsto (fun n => U x ^ (2 * m n - 2) * q x) atTop
        (𝓝 (U x ^ (-2 : ℝ) * q x)) := by
      exact hpow.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => q x) atTop (𝓝 (q x)))
    have hof : Tendsto (fun n => ENNReal.ofReal (U x ^ (2 * m n - 2) * q x)) atTop
        (𝓝 (ENNReal.ofReal (U x ^ (-2 : ℝ) * q x))) := by
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa [I, Uε, max_eq_left hUx] using hof
  have hDCT := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := μ) (F := I) (f := fun x => ENNReal.ofReal (U x ^ (-2 : ℝ) * q x))
    (fun x => ENNReal.ofReal (1 + ε ^ (-4 : ℝ)) * ENNReal.ofReal (q x))
    (Filter.Eventually.of_forall hImeas) (Filter.Eventually.of_forall hdom)
    hboundFinite hpoint
  have hquad (n : ℕ) :
      (fun x => vecDot (U x ^ (m n - 1) • G x)
        (matVecMul (a x) (U x ^ (m n - 1) • G x))) =ᵐ[μ]
      (fun x => U x ^ (2 * m n - 2) * q x) := by
    filter_upwards [hUlower] with x hUx
    have hUxpos : 0 < U x := lt_of_lt_of_le hε hUx
    have hfactor : U x ^ (m n - 1) * U x ^ (m n - 1) =
        U x ^ (2 * m n - 2) := by
      rw [← Real.rpow_add hUxpos]
      congr 1
      ring
    dsimp [q]
    simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    rw [← mul_assoc]
    rw [hfactor]
  have henergySeq (n : ℕ) : weightedEnergy a V
      (fun x => U x ^ (m n - 1) • G x) = ∫⁻ x, I n x ∂μ := by
    change (∫⁻ x, ENNReal.ofReal
      (vecDot (U x ^ (m n - 1) • G x)
        (matVecMul (a x) (U x ^ (m n - 1) • G x))) ∂μ) = _
    apply lintegral_congr_ae
    filter_upwards [hquad n, hUlower] with x hq hx
    simp [I, Uε, max_eq_left hx, hq]
  have henergyLimit : weightedEnergy a V (fun x => U x ^ (-1 : ℝ) • G x) =
      ∫⁻ x, ENNReal.ofReal (U x ^ (-2 : ℝ) * q x) ∂μ := by
    change (∫⁻ x, ENNReal.ofReal
      (vecDot (U x ^ (-1 : ℝ) • G x)
        (matVecMul (a x) (U x ^ (-1 : ℝ) • G x))) ∂μ) = _
    apply lintegral_congr_ae
    filter_upwards [hUlower] with x hx
    have hUxpos : 0 < U x := lt_of_lt_of_le hε hx
    have hfactor : U x ^ (-1 : ℝ) * U x ^ (-1 : ℝ) = U x ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hUxpos]
      congr 1
      ring
    dsimp [q]
    simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    rw [← mul_assoc]
    rw [hfactor]
  have hseq : (fun n => weightedEnergy a V
      (fun x => U x ^ (m n - 1) • G x)) =
      (fun n => ∫⁻ x, I n x ∂μ) := funext henergySeq
  rw [hseq, henergyLimit]
  exact hDCT

/-- Constant scalar multiplication factors exactly out of weighted energy. -/
theorem weightedEnergy_real_smul {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (G : Vec d → Vec d) (c : ℝ) :
    weightedEnergy a V (fun x => c • G x) =
      ENNReal.ofReal (c ^ 2) * weightedEnergy a V G := by
  change (∫⁻ x in V, ENNReal.ofReal
    (vecDot (c • G x) (matVecMul (a x) (c • G x)))) = _
  simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  have hpoint (x : Vec d) : ENNReal.ofReal
      (c * (c * vecDot (G x) (matVecMul (a x) (G x)))) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal
        (vecDot (G x) (matVecMul (a x) (G x))) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    ring
  simp_rw [hpoint]
  change (∫⁻ x in V, ENNReal.ofReal (c ^ 2) *
    ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) =
    ENNReal.ofReal (c ^ 2) * (∫⁻ x in V, ENNReal.ofReal
      (vecDot (G x) (matVecMul (a x) (G x))))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The coefficient left after dividing the power-Caccioppoli estimate by
`m²` converges to one along any nonzero nonpositive sequence tending to zero.
-/
theorem tendsto_powerFactor_sq_div_sq
    (m : ℕ → ℝ) (hmnonpos : ∀ n, m n ≤ 0)
    (hmne : ∀ n, m n ≠ 0)
    (hmtendsto : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n => ENNReal.ofReal
      (powerFactor (m n) ^ 2 / (m n) ^ 2)) atTop (𝓝 1) := by
  have hbase : Tendsto (fun n => 1 - 2 * m n) atTop (𝓝 (1 : ℝ)) := by
    have htwom : Tendsto (fun n => 2 * m n) atTop (𝓝 (0 : ℝ)) := by
      simpa [mul_comm] using hmtendsto.const_mul 2
    simpa using tendsto_const_nhds.sub htwom
  have hbaseSq : Tendsto (fun n => (1 - 2 * m n) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa using hbase.pow 2
  have hinv : Tendsto (fun n => ((1 - 2 * m n) ^ 2)⁻¹) atTop
      (𝓝 (1 : ℝ)) := by
    simpa [Function.comp_def] using
      (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hbaseSq
  have hden (n : ℕ) : 1 - 2 * m n ≠ 0 := by
    have := hmnonpos n
    nlinarith
  have hratio (n : ℕ) : powerFactor (m n) ^ 2 / (m n) ^ 2 =
      ((1 - 2 * m n) ^ 2)⁻¹ := by
    simp only [CoarseDeGiorgi.powerFactor, abs_of_nonpos (hmnonpos n)]
    field_simp [hmne n, hden n]
  have hreal : Tendsto (fun n => powerFactor (m n) ^ 2 / (m n) ^ 2)
      atTop (𝓝 (1 : ℝ)) := by
    convert hinv using 1
    funext n
    exact hratio n
  have hENN : Tendsto
      (fun n => ENNReal.ofReal (powerFactor (m n) ^ 2 / (m n) ^ 2))
      atTop (𝓝 (ENNReal.ofReal 1)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  simpa using hENN

end

end CoarseDeGiorgi.Harnack.LogLimit
