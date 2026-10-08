module

public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.CrossoverExponent
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Harnack.Calculus.Moments
public import CoarseDeGiorgi.Assembly.HybridFractional
public import CoarseDeGiorgi.Weighted.PairOperations
public import CoarseDeGiorgi.Weighted.Identification
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.WeakHarnack

private lemma fiveEighths_subset_unit {d : ℕ} :
    originCube (d := d) (5 / 8) ⊆ originCube 1 := by
  intro x hx i
  dsimp [originCube] at hx ⊢
  constructor <;> linarith [hx i]

/-- The weak supersolution's `MemH1a` field implies local `L¹` integrability
on the cube used by the ε-limit argument.
-/
theorem weightedSupersolution_integrable_fiveEighths {d : ℕ} [NeZero d]
    {a : CoeffField d} (ha : IsWeightedCoeffOn (originCube (d := d) 1) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSupersolution a (originCube (d := d) 1) u G) :
    IntegrableOn u (originCube (d := d) (5 / 8)) := by
  have hunit := Assembly.hybrid_unitCube_domain (d := d)
  have hneg : MemH1a a (originCube (d := d) 1) (-u) (-G) := by
    change IsWeightedSubsolution a (originCube 1) (-u) (-G) at hu
    exact hu.1
  have hmem := Weighted.MemH1a.neg hunit.1 hunit.2 ha hneg
  simpa only [Pi.neg_apply, neg_neg] using
    (Weighted.memH1a_memW11 hunit.1 hunit.2 ha hmem).1.mono_set
      fiveEighths_subset_unit

/-- The crossover exponent `crossoverExponent` is the real expression `c / sqrt (1+Θ)`
on the finite-contrast range. -/
theorem crossoverExponent_eq_div_sqrt {d : ℕ} (c : ℝ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (s t p q : ℝ) (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hΘtop : contrast a ha s t p q hs ht hp hq < ⊤) :
    crossoverExponent c a ha s t p q hs ht hp hq =
      c / Real.sqrt (1 + (contrast a ha s t p q hs ht hp hq).toReal) := by
  let Θ := contrast a ha s t p q hs ht hp hq
  have hΘtop' : Θ < ⊤ := hΘtop
  have hsumtop : 1 + Θ < ⊤ := ENNReal.add_lt_top.mpr ⟨by simp, hΘtop'⟩
  have hsumreal : (1 + Θ).toReal = 1 + Θ.toReal :=
    ENNReal.toReal_add (by simp) hΘtop'.ne
  have hrealpow : ((1 + Θ).rpow (-(1 / 2 : ℝ))).toReal =
      (Real.sqrt (1 + Θ.toReal))⁻¹ := by
    change ((1 + Θ) ^ (-(1 / 2 : ℝ))).toReal =
      (Real.sqrt (1 + Θ.toReal))⁻¹
    rw [← ENNReal.toReal_rpow, hsumreal,
      Real.rpow_neg (by positivity : 0 ≤ 1 + Θ.toReal) (1 / 2 : ℝ),
      ← Real.sqrt_eq_rpow]
  unfold crossoverExponent
  change c * ((1 + Θ).rpow (-(1 / 2 : ℝ))).toReal =
    c / Real.sqrt (1 + Θ.toReal)
  rw [hrealpow, div_eq_mul_inv]

/-- Positivity of the crossover exponent on finite contrast data. -/
theorem crossoverExponent_pos {d : ℕ} (c : ℝ) (hc : 0 < c)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (s t p q : ℝ) (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hΘtop : contrast a ha s t p q hs ht hp hq < ⊤) :
    0 < crossoverExponent c a ha s t p q hs ht hp hq := by
  rw [crossoverExponent_eq_div_sqrt c a ha s t p q hs ht hp hq hΘtop]
  apply div_pos hc
  apply Real.sqrt_pos.2
  have hθnonneg : 0 ≤ (contrast a ha s t p q hs ht hp hq).toReal := ENNReal.toReal_nonneg
  linarith

/-- Dominated convergence removes the positive shift from a uniform weak moment
estimate. The integrability premise is supplied from the supersolution's
weighted `H¹` membership through the source's weighted-to-`W¹,¹` identification.
-/
theorem normalizedLpMoment_epsilon_limit {d : ℕ} (V : Set (Vec d))
    (u : Vec d → ℝ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hVpos : 0 < volume V) (hVtop : volume V < ⊤)
    (hu_nonneg : 0 ≤ᵐ[volume.restrict V] u)
    (hu_int : IntegrableOn u V)
    (A m : ℝ≥0∞) (hApos : 0 < A) (hAtop : A < ⊤)
    (hε : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      normalizedLpMoment η hη V (fun x => u x + ε) ≤
        A * (m + ENNReal.ofReal ε)) :
    normalizedLpMoment η hη V u ≤ A * m := by
  by_cases hm : m = ⊤
  · calc
      normalizedLpMoment η hη V u ≤ ⊤ := le_top
      _ = A * m := by
        rw [hm]
        simp [hApos.ne']
  let εseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < εseq n := by
    dsimp [εseq]
    positivity
  have hεle (n : ℕ) : εseq n ≤ 1 := by
    dsimp [εseq]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_le_one (by positivity)]
    linarith
  have hεlim : Tendsto εseq atTop (𝓝 (0 : ℝ)) := by
    simpa [εseq] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let μ : Measure (Vec d) := volume.restrict V
  let bound : Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((fun _ : Vec d => (1 : ℝ)) + u) x)
  let Fn : ℕ → Vec d → ℝ≥0∞ := fun n x =>
    (ENNReal.ofReal |u x + εseq n|).rpow η
  let F : Vec d → ℝ≥0∞ := fun x => (ENNReal.ofReal |u x|).rpow η
  have hu_meas : AEStronglyMeasurable u μ := hu_int.aestronglyMeasurable
  have hsum_int : IntegrableOn ((fun _ : Vec d => (1 : ℝ)) + u) V := by
    have hone : IntegrableOn (fun _ : Vec d => (1 : ℝ)) V :=
      integrableOn_const hVtop.ne
    exact hone.add hu_int
  have hsum_int' : Integrable ((fun _ : Vec d => (1 : ℝ)) + u) μ := by
    simpa [μ, IntegrableOn] using hsum_int
  have hbound_finite : ∫⁻ x, bound x ∂μ < ⊤ := by
    simpa [bound] using hsum_int'.lintegral_lt_top
  have hFn_meas : ∀ n, AEMeasurable (Fn n) μ := by
    intro n
    have hshift : AEMeasurable (fun x => u x + εseq n) μ :=
      (hu_meas.add_const _).aemeasurable
    have habs : AEMeasurable (fun x => |u x + εseq n|) μ :=
      continuous_abs.measurable.comp_aemeasurable hshift
    have hpow : AEMeasurable (fun x => |u x + εseq n| ^ η) μ :=
      (Real.continuous_rpow_const hη.le).measurable.comp_aemeasurable habs
    have hrepr : Fn n = fun x => ENNReal.ofReal (|u x + εseq n| ^ η) := by
      funext x
      dsimp [Fn]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hη.le]
    rw [hrepr]
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable hpow
  have hFn_bound : ∀ n, Fn n ≤ᵐ[μ] bound := by
    intro n
    filter_upwards [hu_nonneg] with x hx
    have hu0 : 0 ≤ u x := hx
    have hbase0 : 0 ≤ u x + εseq n := add_nonneg hu0 (le_of_lt (hεpos n))
    have hbase_le : u x + εseq n ≤ 1 + u x := by linarith [hεle n]
    have hpow_le : (u x + εseq n) ^ η ≤ 1 + u x := by
      by_cases hbase : u x + εseq n ≤ 1
      · calc
          (u x + εseq n) ^ η ≤ 1 := Real.rpow_le_one hbase0 hbase hη.le
          _ ≤ 1 + u x := by linarith
      · have hbase1 : 1 ≤ u x + εseq n := le_of_not_ge hbase
        calc
          (u x + εseq n) ^ η ≤ u x + εseq n :=
            Real.rpow_le_self_of_one_le hbase1 hη1
          _ ≤ 1 + u x := hbase_le
    have hFn_eq : Fn n x = ENNReal.ofReal ((u x + εseq n) ^ η) := by
      dsimp [Fn]
      rw [abs_of_nonneg hbase0, ENNReal.ofReal_rpow_of_nonneg hbase0 hη.le]
    rw [hFn_eq]
    exact ENNReal.ofReal_le_ofReal hpow_le
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)) := by
    filter_upwards [hu_nonneg] with x hx
    have hreal : Tendsto (fun n => u x + εseq n) atTop (𝓝 (u x)) := by
      simpa using tendsto_const_nhds.add hεlim
    have hpow : Tendsto (fun n => (u x + εseq n) ^ η) atTop (𝓝 (u x ^ η)) :=
      hreal.rpow_const (Or.inr hη.le)
    have hcast : Tendsto (fun n => ENNReal.ofReal ((u x + εseq n) ^ η)) atTop
        (𝓝 (ENNReal.ofReal (u x ^ η))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpow
    have hFnEq (n : ℕ) : Fn n x = ENNReal.ofReal ((u x + εseq n) ^ η) := by
      have hbase : 0 ≤ u x + εseq n := add_nonneg hx (le_of_lt (hεpos n))
      dsimp [Fn]
      rw [abs_of_nonneg hbase, ENNReal.ofReal_rpow_of_nonneg hbase hη.le]
    have hFEq : F x = ENNReal.ofReal (u x ^ η) := by
      dsimp [F]
      rw [abs_of_nonneg hx, ENNReal.ofReal_rpow_of_nonneg hx hη.le]
    simpa only [hFnEq, hFEq] using hcast
  have hDCT := tendsto_lintegral_of_dominated_convergence' bound hFn_meas
    hFn_bound hbound_finite.ne hpoint
  have hvolinv_top : (volume V)⁻¹ ≠ ⊤ := by
    exact ENNReal.inv_ne_top.2 hVpos.ne'
  have hscaled : Tendsto
      (fun n => (volume V)⁻¹ * ∫⁻ x, Fn n x ∂μ) atTop
      (𝓝 ((volume V)⁻¹ * ∫⁻ x, F x ∂μ)) :=
    ENNReal.Tendsto.const_mul hDCT (Or.inr hvolinv_top)
  have hnormalized_pow (f : Vec d → ℝ) (hf_nonneg : 0 ≤ᵐ[μ] f) :
      (normalizedLpMoment η hη V f) ^ η =
        (volume V)⁻¹ * ∫⁻ x, (ENNReal.ofReal |f x|).rpow η ∂μ := by
    rw [CoarseDeGiorgi.Harnack.Calculus.normalizedLpMoment_eq_literal_integral]
    have hexp : 1 / η = η⁻¹ := by ring
    rw [hexp]
    exact ENNReal.rpow_inv_rpow hη.ne' _
  have hleftLim : Tendsto
      (fun n => (normalizedLpMoment η hη V (fun x => u x + εseq n)) ^ η)
      atTop (𝓝 ((normalizedLpMoment η hη V u) ^ η)) := by
    have hrewrite (n : ℕ) :
        (normalizedLpMoment η hη V (fun x => u x + εseq n)) ^ η =
          (volume V)⁻¹ * ∫⁻ x, Fn n x ∂μ := by
      rw [hnormalized_pow _ (by
        filter_upwards [hu_nonneg] with x hx
        exact add_nonneg hx (le_of_lt (hεpos n)))]
    have hrewriteLim :
        (normalizedLpMoment η hη V u) ^ η =
          (volume V)⁻¹ * ∫⁻ x, F x ∂μ := by
      rw [hnormalized_pow u hu_nonneg]
    simpa only [hrewrite, hrewriteLim] using hscaled
  have hmreal : m = ENNReal.ofReal m.toReal := (ENNReal.ofReal_toReal hm).symm
  have hAreal : A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAtop.ne).symm
  have hrightLim : Tendsto
      (fun n => (A * (m + ENNReal.ofReal (εseq n))) ^ η) atTop
      (𝓝 ((A * m) ^ η)) := by
    have hrealBase : Tendsto
        (fun n => A.toReal * (m.toReal + εseq n)) atTop
        (𝓝 (A.toReal * m.toReal)) := by
      simpa using (tendsto_const_nhds.add hεlim).const_mul A.toReal
    have hrealPow := hrealBase.rpow_const (Or.inr hη.le)
    have hcast := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrealPow
    have hrewrite (n : ℕ) :
        (A * (m + ENNReal.ofReal (εseq n))) ^ η =
          ENNReal.ofReal ((A.toReal * (m.toReal + εseq n)) ^ η) := by
      calc
        _ = (ENNReal.ofReal A.toReal *
            (ENNReal.ofReal m.toReal + ENNReal.ofReal (εseq n))) ^ η := by
          congr 1
          conv_lhs => rw [hAreal, hmreal]
        _ = (ENNReal.ofReal (A.toReal * (m.toReal + εseq n))) ^ η := by
          rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (le_of_lt (hεpos n)),
            ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        _ = ENNReal.ofReal ((A.toReal * (m.toReal + εseq n)) ^ η) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hη.le
    have htarget : (A * m) ^ η = ENNReal.ofReal ((A.toReal * m.toReal) ^ η) := by
      calc
        _ = (ENNReal.ofReal A.toReal * ENNReal.ofReal m.toReal) ^ η := by
          congr 1
          conv_lhs => rw [hAreal, hmreal]
        _ = (ENNReal.ofReal (A.toReal * m.toReal)) ^ η := by
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        _ = ENNReal.ofReal ((A.toReal * m.toReal) ^ η) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hη.le
    have hcast' : Tendsto
        (fun n => ENNReal.ofReal ((A.toReal * (m.toReal + εseq n)) ^ η)) atTop
        (𝓝 (ENNReal.ofReal ((A.toReal * m.toReal) ^ η))) := by
      change Tendsto
        (fun n => ENNReal.ofReal ((A.toReal * (m.toReal + εseq n)) ^ η)) atTop
        (𝓝 (ENNReal.ofReal ((A.toReal * m.toReal) ^ η))) at hcast
      exact hcast
    have hfunEq : (fun n => (A * (m + ENNReal.ofReal (εseq n))) ^ η) =
        fun n => ENNReal.ofReal ((A.toReal * (m.toReal + εseq n)) ^ η) := by
      funext n
      exact hrewrite n
    rw [hfunEq, htarget]
    exact hcast'
  have hpowBound : ∀ n, (normalizedLpMoment η hη V
      (fun x => u x + εseq n)) ^ η ≤
        (A * (m + ENNReal.ofReal (εseq n))) ^ η := by
    intro n
    exact ENNReal.rpow_le_rpow
      (hε (εseq n) (hεpos n) (hεle n)) hη.le
  have hlimPow := le_of_tendsto_of_tendsto hleftLim hrightLim
    (Filter.Eventually.of_forall hpowBound)
  exact (ENNReal.rpow_le_rpow_iff hη).mp hlimPow

end CoarseDeGiorgi.Harnack.WeakHarnack
