module

public import CoarseDeGiorgi.Assembly.LocalBoundedness
public import CoarseDeGiorgi.Weighted.TestingNorms
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

namespace CoarseDeGiorgi.TheoremA

lemma originCube_mono {d : ℕ} {ρ R : ℝ} (hρR : ρ ≤ R) :
    CoarseDeGiorgi.originCube (d := d) ρ ⊆ CoarseDeGiorgi.originCube (d := d) R := by
  intro x hx i
  constructor <;> dsimp [CoarseDeGiorgi.originCube] at * <;> linarith only [hx i, hρR]

/-! Passing the interior `L^η` estimates of Corollary B to the endpoint cube of side one. -/

/-- A sequence of increasing measurable restrictions exhausting a measure space
has convergent finite-exponent `eLpNorm`; this also applies when the limit is
infinite. -/
private theorem tendsto_eLpNorm_restrict_iUnion {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : ℕ → Set α} (hSmeas : ∀ n, MeasurableSet (S n))
    (hSmono : Monotone S) {U : Set α} (hSunion : ⋃ n, S n = U)
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {r : ℝ≥0∞}
    (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    Tendsto (fun n => eLpNorm f r (μ.restrict (S n))) atTop
      (𝓝 (eLpNorm f r (μ.restrict U))) := by
  have hpow : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
  let g : α → ℝ≥0∞ := fun x => ‖f x‖ₑ ^ r.toReal
  have hnorm : AEStronglyMeasurable (fun x => ‖f x‖ₑ) μ :=
    continuous_enorm.comp_aestronglyMeasurable hf
  have hg : AEMeasurable g μ :=
    (ENNReal.continuous_rpow_const.comp_aestronglyMeasurable hnorm).aemeasurable
  let gn : ℕ → α → ℝ≥0∞ := fun n => (S n).indicator g
  have hgn (n : ℕ) : AEMeasurable (gn n) μ :=
    hg.indicator (hSmeas n)
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n => gn n x) := by
    filter_upwards with x
    intro n m hnm
    by_cases hx : x ∈ S n
    · have : x ∈ S m := hSmono hnm hx
      simp [gn, hx, this]
    · simp [gn, hx]
  let gU : α → ℝ≥0∞ := U.indicator g
  have hUmeas : MeasurableSet U := by
    rw [← hSunion]
    exact MeasurableSet.iUnion hSmeas
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => gn n x) atTop (𝓝 (gU x)) := by
    filter_upwards with x
    by_cases hxU : x ∈ U
    · have hxUnion : x ∈ ⋃ n, S n := by rw [hSunion]; exact hxU
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxUnion
      have heq : (fun m => gn m x) =ᶠ[atTop] fun _ => gU x := by
        filter_upwards [eventually_ge_atTop n] with m hm
        simp [gU, gn, hxU, hSmono (show n ≤ m from hm) hn]
      exact (tendsto_congr' heq).mpr tendsto_const_nhds
    · have heq : (fun m => gn m x) = fun _ => gU x := by
        funext m
        have hxSm : x ∉ S m := by
          intro hx
          have : x ∈ ⋃ n, S n := Set.mem_iUnion.mpr ⟨m, hx⟩
          rw [hSunion] at this
          exact hxU this
        simp [gU, gn, hxSm, hxU]
      rw [heq]
      exact tendsto_const_nhds
  have hlin := lintegral_tendsto_of_tendsto_of_monotone hgn hmono hpoint
  have hnform (n : ℕ) : eLpNorm f r (μ.restrict (S n)) =
      (∫⁻ x, gn n x ∂μ) ^ (1 / r.toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt (hf.mono_measure
      Measure.restrict_le_self), ← lintegral_indicator (hSmeas n)]
  have hform : eLpNorm f r (μ.restrict U) =
      (∫⁻ x, gU x ∂μ) ^ (1 / r.toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt (hf.mono_measure
      Measure.restrict_le_self), ← lintegral_indicator hUmeas]
  rw [show (fun n => eLpNorm f r (μ.restrict (S n))) =
      (fun n => (∫⁻ x, gn n x ∂μ) ^ (1 / r.toReal)) by
        funext n; rw [hnform]]
  rw [hform]
  have hcont := ENNReal.continuous_rpow_const (y := (1 / r.toReal : ℝ))
  exact hcont.tendsto _ |>.comp hlin

private noncomputable def endpointRadius (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

private lemma tendsto_endpointRadius :
    Tendsto endpointRadius atTop (𝓝 (1 : ℝ)) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1
    · ext n
      simp [Nat.cast_add]
      ring
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop
      (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 : ℝ))
  exact h

private lemma endpointRadius_mono : Monotone endpointRadius := by
  intro n m hnm
  dsimp [endpointRadius]
  gcongr

private lemma endpointRadius_lt_one (n : ℕ) : endpointRadius n < 1 := by
  dsimp [endpointRadius]
  have : 0 < (n : ℝ) + 2 := by positivity
  linarith [one_div_pos.mpr this]

private lemma endpointRadius_le_one (n : ℕ) : endpointRadius n ≤ 1 :=
  (endpointRadius_lt_one n).le

private lemma measurable_originCube_local {d : ℕ} (ρ : ℝ) :
    MeasurableSet (CoarseDeGiorgi.originCube (d := d) ρ) := by
  have hopen : IsOpen (CoarseDeGiorgi.originCube (d := d) ρ) := by
    change IsOpen {x : Vec d | ∀ i, (-(ρ / 2)) < x i ∧ x i < ρ / 2}
    simp only [← Set.iInter_ofPred]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_Ioo.preimage (continuous_apply i)
  exact hopen.measurableSet

private lemma endpointCubes_iUnion {d : ℕ} :
    (⋃ n, CoarseDeGiorgi.originCube (d := d) (endpointRadius n)) =
      CoarseDeGiorgi.originCube (d := d) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact originCube_mono (endpointRadius_le_one n) hn
  · intro x hx
    have hhalf : Tendsto (fun n => endpointRadius n / 2) atTop (𝓝 (1 / 2 : ℝ)) := by
      simpa using tendsto_endpointRadius.div_const 2
    have hcoord : ∀ i : Fin d, ∀ᶠ n : ℕ in atTop,
        |x i| < endpointRadius n / 2 := by
      intro i
      have hxi : |x i| < (1 : ℝ) / 2 := by
        have := hx i
        rw [abs_lt]
        constructor <;> linarith
      exact (tendsto_order.1 hhalf).1 _ hxi
    have hall : ∀ᶠ n : ℕ in atTop, ∀ i : Fin d,
        |x i| < endpointRadius n / 2 := eventually_all.2 hcoord
    obtain ⟨n, hn⟩ := hall.exists
    apply Set.mem_iUnion.mpr ⟨n, ?_⟩
    intro i
    have hxi := abs_lt.mp (hn i)
    constructor <;> linarith

/-- Pass an interior family of `Lη` estimates to the limiting cube. -/
theorem eta_endpoint_of_interior {d : ℕ} {u : Vec d → ℝ} {ρ η α β : ℝ}
    {B C : ℝ≥0∞} (hρ1 : ρ < 1) (hη : 0 < η) (hβ : 0 ≤ β)
    (hB : 0 < B) (hBtop : B < ⊤) (hC : 0 < C) (hCtop : C < ⊤)
    (hf : AEStronglyMeasurable (positivePart u)
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)))
    (hinner : ∀ R' : ℝ, ρ < R' → R' < 1 →
      eLpNorm (positivePart u) ⊤
          (volume.restrict (CoarseDeGiorgi.originCube (d := d) ρ)) ≤
        C * (ENNReal.ofReal (R' - ρ)).rpow α * B.rpow β *
          eLpNorm (positivePart u) (ENNReal.ofReal η)
            (volume.restrict (CoarseDeGiorgi.originCube (d := d) R'))) :
    eLpNorm (positivePart u) ⊤
        (volume.restrict (CoarseDeGiorgi.originCube (d := d) ρ)) ≤
      C * (ENNReal.ofReal (1 - ρ)).rpow α * B.rpow β *
        eLpNorm (positivePart u) (ENNReal.ofReal η)
          (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)) := by
  let S : ℕ → Set (Vec d) := fun n => CoarseDeGiorgi.originCube (endpointRadius n)
  let U : Set (Vec d) := CoarseDeGiorgi.originCube 1
  let T : ℕ → Set (Vec d) := fun n => S n ∪ Uᶜ
  have hmono : Monotone S := by
    intro n m hnm
    exact originCube_mono (endpointRadius_mono hnm)
  have hTmono : Monotone T := by
    intro n m hnm x hx
    rcases hx with hx | hx
    · exact Or.inl (hmono hnm hx)
    · exact Or.inr hx
  have hUmeas : MeasurableSet U := measurable_originCube_local 1
  have hmeas : ∀ n, MeasurableSet (S n) := by
    intro n
    change MeasurableSet (CoarseDeGiorgi.originCube (endpointRadius n))
    exact measurable_originCube_local (endpointRadius n)
  have hTmeas : ∀ n, MeasurableSet (T n) := by
    intro n
    exact (hmeas n).union hUmeas.compl
  have hSsubset (n : ℕ) : S n ⊆ U :=
    originCube_mono (endpointRadius_le_one n)
  have hTinter (n : ℕ) : T n ∩ U = S n := by
    ext x
    constructor
    · rintro ⟨hxT, hxU⟩
      rcases hxT with hxS | hxnotU
      · exact hxS
      · exact (hxnotU hxU).elim
    · intro hxS
      exact ⟨Or.inl hxS, hSsubset n hxS⟩
  have hSunion : ⋃ n, T n = Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      by_cases hx : x ∈ U
      · have hx' : x ∈ ⋃ n, S n := by
          rw [endpointCubes_iUnion]
          exact hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx'
        exact Set.mem_iUnion.mpr ⟨n, Or.inl hn⟩
      · exact Set.mem_iUnion.mpr ⟨0, Or.inr hx⟩
  have hnormTendsto' : Tendsto
      (fun n => eLpNorm (positivePart u) (ENNReal.ofReal η)
        ((volume.restrict U).restrict (T n))) atTop
      (𝓝 (eLpNorm (positivePart u) (ENNReal.ofReal η)
        ((volume.restrict U).restrict Set.univ))) := by
    exact tendsto_eLpNorm_restrict_iUnion hTmeas hTmono hSunion
      hf (ENNReal.ofReal_pos.mpr hη).ne' ENNReal.ofReal_ne_top
  have hseqEq (n : ℕ) :
      (volume.restrict U).restrict (T n) = volume.restrict (S n) := by
    rw [volume.restrict_restrict (hTmeas n), hTinter n]
  have hnormTendsto : Tendsto
      (fun n => eLpNorm (positivePart u) (ENNReal.ofReal η)
        (volume.restrict (S n))) atTop
      (𝓝 (eLpNorm (positivePart u) (ENNReal.ofReal η)
        (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)))) := by
    have heq : (fun n => eLpNorm (positivePart u) (ENNReal.ofReal η)
        (volume.restrict (S n))) = fun n => eLpNorm (positivePart u)
          (ENNReal.ofReal η) ((volume.restrict U).restrict (T n)) := by
      funext n
      rw [← hseqEq n]
    rw [heq]
    simpa [U] using hnormTendsto'
  by_cases hfull : eLpNorm (positivePart u) (ENNReal.ofReal η)
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)) < ⊤
  · let gapPow : ℕ → ℝ≥0∞ := fun n =>
      (ENNReal.ofReal (endpointRadius n - ρ)).rpow α
    have hgapReal : Tendsto (fun n => endpointRadius n - ρ) atTop (𝓝 (1 - ρ)) := by
      simpa using tendsto_endpointRadius.sub_const ρ
    have hgap : Tendsto (fun n => ENNReal.ofReal (endpointRadius n - ρ)) atTop
        (𝓝 (ENNReal.ofReal (1 - ρ))) :=
      (ENNReal.continuous_ofReal.tendsto (1 - ρ)).comp hgapReal
    have hgapPow : Tendsto gapPow atTop
        (𝓝 ((ENNReal.ofReal (1 - ρ)).rpow α)) := by
      exact hgap.ennrpow_const α
    have hBpowtop : B.rpow β < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg hβ hBtop.ne
    have hgapB : Tendsto (fun n => gapPow n * B.rpow β) atTop
        (𝓝 ((ENNReal.ofReal (1 - ρ)).rpow α * B.rpow β)) :=
      ENNReal.Tendsto.mul_const hgapPow (Or.inr hBpowtop.ne)
    have hgaplimtop :
        (ENNReal.ofReal (1 - ρ)).rpow α * B.rpow β < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.rpow_ne_top_of_ne_zero
          (ENNReal.ofReal_pos.mpr (sub_pos.mpr hρ1)).ne' ENNReal.ofReal_ne_top |>.lt_top
      · exact hBpowtop
    have hgapnorm : Tendsto
        (fun n => gapPow n * B.rpow β *
          eLpNorm (positivePart u) (ENNReal.ofReal η) (volume.restrict (S n))) atTop
        (𝓝 ((ENNReal.ofReal (1 - ρ)).rpow α * B.rpow β *
          eLpNorm (positivePart u) (ENNReal.ofReal η)
            (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)))) := by
      exact ENNReal.Tendsto.mul hgapB (Or.inr hfull.ne) hnormTendsto
        (Or.inr hgaplimtop.ne)
    have hRHS : Tendsto (fun n => C * gapPow n * B.rpow β *
        eLpNorm (positivePart u) (ENNReal.ofReal η) (volume.restrict (S n))) atTop
        (𝓝 (C * (ENNReal.ofReal (1 - ρ)).rpow α * B.rpow β *
          eLpNorm (positivePart u) (ENNReal.ofReal η)
            (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)))) := by
      simpa [mul_assoc] using
        ENNReal.Tendsto.const_mul (a := C) hgapnorm (Or.inr hCtop.ne)
    have hlarge : ∀ᶠ n : ℕ in atTop, ρ < endpointRadius n :=
      (tendsto_order.1 tendsto_endpointRadius).1 ρ hρ1
    have hbounds : ∀ᶠ n : ℕ in atTop,
        eLpNorm (positivePart u) ⊤
          (volume.restrict (CoarseDeGiorgi.originCube (d := d) ρ)) ≤
        C * gapPow n * B.rpow β *
          eLpNorm (positivePart u) (ENNReal.ofReal η) (volume.restrict (S n)) := by
      filter_upwards [hlarge] with n hn
      simpa [gapPow, S, mul_assoc] using hinner (endpointRadius n) hn
        (endpointRadius_lt_one n)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hRHS hbounds
  · have hfulltop : eLpNorm (positivePart u) (ENNReal.ofReal η)
        (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)) = ⊤ := le_antisymm le_top (le_of_not_gt hfull)
    have hgapbase : 0 < ENNReal.ofReal (1 - ρ) :=
      ENNReal.ofReal_pos.mpr (sub_pos.mpr hρ1)
    have hgapbasetop : ENNReal.ofReal (1 - ρ) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hgapPowpos : 0 < (ENNReal.ofReal (1 - ρ)).rpow α :=
      ENNReal.rpow_pos hgapbase hgapbasetop
    have hBpowpos : 0 < B.rpow β := ENNReal.rpow_pos hB hBtop.ne
    have hcoef : C * (ENNReal.ofReal (1 - ρ)).rpow α * B.rpow β ≠ 0 :=
      mul_ne_zero (mul_ne_zero hC.ne' hgapPowpos.ne') hBpowpos.ne'
    rw [hfulltop, ENNReal.mul_top hcoef]
    exact le_top

end CoarseDeGiorgi.TheoremA
