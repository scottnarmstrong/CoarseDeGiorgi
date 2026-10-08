module

public import CoarseDeGiorgi.Whitney.Extension.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Averages over measurable subsets of the cube surface -/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

variable {d : ℕ}

theorem surfaceMeasure_ae_mem (τ : ℝ) (hτ : 0 ≤ τ) :
    ∀ᵐ x ∂surfaceMeasure (d := d) τ, x ∈ cubeSurface τ :=
  Foundations.FracGeometry.surfaceMeasure_ae_surface hτ

theorem isCompact_cubeSurface (τ : ℝ) : IsCompact (cubeSurface (d := d) τ) := by
  simpa only [cubeSurface, Metric.sphere, dist_zero_right] using
    isCompact_sphere (0 : Vec d) (τ / 2)

theorem integrable_of_continuousOn {τ : ℝ} (hτ : 0 ≤ τ) {f : Vec d → ℝ}
    (hf : ContinuousOn f (cubeSurface τ)) : Integrable f (surfaceMeasure τ) := by
  let := seedSurfaceMeasure_finite (d := d) τ
  have hi := hf.integrableOn_compact (μ := surfaceMeasure τ) (isCompact_cubeSurface τ)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [surfaceMeasure_ae_mem (d := d) τ hτ] with x hx
  exact fun hn => (hn hx).elim

theorem average_mem_Icc_of_ae {ν : Measure (Vec d)} [IsFiniteMeasure ν] {f : Vec d → ℝ}
    {m M : ℝ} (hm : m ≤ 0) (hM : 0 ≤ M) (hf : ∀ᵐ y ∂ν, m ≤ f y ∧ f y ≤ M) :
    ⨍ x, f x ∂ν ∈ Icc m M := by
  by_cases h0 : ν = 0
  · subst h0
    simp [hm, hM]
  by_cases hi : Integrable f ν
  · have : NeZero ν := ⟨h0⟩
    exact (convex_Icc m M).average_mem isClosed_Icc (hf.mono fun _ h => h) hi
  · rw [average_eq, integral_undef hi]
    simp [hm, hM]

/-- bound by an a.e. bound -/
theorem abs_average_le {τ : ℝ} (P : Set (Vec d)) {f : Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ᵐ y ∂surfaceMeasure τ, |f y| ≤ B) :
    |⨍ x in P, f x ∂surfaceMeasure τ| ≤ B := by
  let := seedSurfaceMeasure_finite (d := d) τ
  have := average_mem_Icc_of_ae (ν := (surfaceMeasure τ).restrict P) (f := f)
    (m := -B) (M := B) (by linarith) hB
    (ae_restrict_of_ae (hf.mono fun y h => abs_le.mp h))
  exact abs_le.mpr this

/-- values of the average lie in `[m, M]` (`m ≤ 0 ≤ M`) -/
theorem average_mem_Icc {τ : ℝ} (hτ : 0 ≤ τ) (P : Set (Vec d)) {f : Vec d → ℝ} {m M : ℝ}
    (hm : m ≤ 0) (hM : 0 ≤ M) (hf : ∀ y ∈ cubeSurface τ, m ≤ f y ∧ f y ≤ M) :
    m ≤ ⨍ x in P, f x ∂surfaceMeasure τ ∧ ⨍ x in P, f x ∂surfaceMeasure τ ≤ M := by
  let := seedSurfaceMeasure_finite (d := d) τ
  exact average_mem_Icc_of_ae (ν := (surfaceMeasure τ).restrict P) hm hM
    (ae_restrict_of_ae ((surfaceMeasure_ae_mem (d := d) τ hτ).mono fun y hy => hf y hy))

/-- linearity of the average for functions integrable for the surface measure -/
theorem average_linear {τ : ℝ} (P : Set (Vec d)) {f₁ f₂ : Vec d → ℝ}
    (h₁ : Integrable f₁ (surfaceMeasure τ)) (h₂ : Integrable f₂ (surfaceMeasure τ)) (c₁ c₂ : ℝ) :
    ⨍ x in P, (c₁ * f₁ x + c₂ * f₂ x) ∂surfaceMeasure τ =
      c₁ * ⨍ x in P, f₁ x ∂surfaceMeasure τ + c₂ * ⨍ x in P, f₂ x ∂surfaceMeasure τ := by
  simp only [average_eq, smul_eq_mul]
  rw [integral_add (h₁.restrict.const_mul c₁) (h₂.restrict.const_mul c₂), integral_const_mul,
    integral_const_mul]
  ring

theorem abs_average_sub_le {τ : ℝ} (hτ : 0 ≤ τ) {P : Set (Vec d)} (hP : MeasurableSet P)
    (_hPs : P ⊆ cubeSurface τ) (hP0 : 0 < surfaceMeasure τ P) {f : Vec d → ℝ}
    (hf : ContinuousOn f (cubeSurface τ)) {c K : ℝ} (h : ∀ x ∈ P, |f x - c| ≤ K) :
    |(⨍ x in P, f x ∂surfaceMeasure τ) - c| ≤ K := by
  let := seedSurfaceMeasure_finite (d := d) τ
  have hne : (surfaceMeasure τ).restrict P ≠ 0 := by
    intro h0
    have := Measure.restrict_apply_univ (μ := surfaceMeasure τ) P
    rw [h0] at this
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    exact hP0.ne this
  have hK : 0 ≤ K := by
    obtain ⟨x, hx⟩ : P.Nonempty := by
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty] at hn
      simp [hn] at hP0
    exact (abs_nonneg _).trans (h x hx)
  have : NeZero ((surfaceMeasure τ).restrict P) := ⟨hne⟩
  have hmem := (convex_Icc (c - K) (c + K)).average_mem isClosed_Icc
    ((ae_restrict_iff' hP).mpr (Filter.Eventually.of_forall fun x hx => by
      have := abs_le.mp (h x hx); constructor <;> linarith [this.1, this.2]))
    (integrable_of_continuousOn hτ hf).restrict
  have := hmem
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

/-- difference of two averages when all pairwise differences are bounded -/
theorem abs_average_sub_average_le {τ : ℝ} (hτ : 0 ≤ τ) {P Q : Set (Vec d)}
    (hP : MeasurableSet P) (hPs : P ⊆ cubeSurface τ) (hP0 : 0 < surfaceMeasure τ P)
    (hQ : MeasurableSet Q) (hQs : Q ⊆ cubeSurface τ) (hQ0 : 0 < surfaceMeasure τ Q)
    {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {K : ℝ}
    (h : ∀ x ∈ P, ∀ y ∈ Q, |f x - f y| ≤ K) :
    |(⨍ x in P, f x ∂surfaceMeasure τ) - ⨍ y in Q, f y ∂surfaceMeasure τ| ≤ K := by
  have h1 : ∀ y ∈ Q, |(⨍ x in P, f x ∂surfaceMeasure τ) - f y| ≤ K := fun y hy =>
    abs_average_sub_le hτ hP hPs hP0 hf (fun x hx => h x hx y hy)
  rw [abs_sub_comm]
  exact abs_average_sub_le hτ hQ hQs hQ0 hf (fun y hy => by rw [abs_sub_comm]; exact h1 y hy)

/-! ### Jensen -/

theorem convexOn_abs_rpow {r : ℝ} (hr : 1 ≤ r) :
    ConvexOn ℝ univ (fun x : ℝ => |x| ^ r) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have ht : |a * x + b * y| ≤ a * |x| + b * |y| := by
    calc
      _ ≤ |a * x| + |b * y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  exact (Real.rpow_le_rpow (abs_nonneg _) ht (by linarith only [hr])).trans
    ((convexOn_rpow hr).2 (abs_nonneg x) (abs_nonneg y) ha hb hab)

theorem average_sub_const' {ν : Measure (Vec d)} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {f : Vec d → ℝ} (hf : Integrable f ν) (c : ℝ) :
    ⨍ x, (f x - c) ∂ν = ⨍ x, f x ∂ν - c := by
  have hm : 0 < ν.real univ := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr (Measure.measure_univ_ne_zero.mpr hν), measure_lt_top _ _⟩
  simp only [average_eq, smul_eq_mul]
  rw [integral_sub hf (integrable_const c), integral_const]
  simp only [smul_eq_mul]
  field_simp

theorem abs_rpow_sub_average_le {ν : Measure (Vec d)} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {r c : ℝ} (hr : 1 ≤ r) {f : Vec d → ℝ} (hf : Integrable f ν)
    (hfr : Integrable (fun x => |f x - c| ^ r) ν) :
    |⨍ x, f x ∂ν - c| ^ r ≤ (ν.real univ)⁻¹ * ∫ x, |f x - c| ^ r ∂ν := by
  have hg : Continuous (fun x : ℝ => |x| ^ r) :=
    continuous_abs.rpow_const (fun _ => Or.inr (by linarith only [hr]))
  have : NeZero ν := ⟨hν⟩
  have hj : |⨍ x, (f x - c) ∂ν| ^ r ≤ ⨍ x, |f x - c| ^ r ∂ν :=
    (convexOn_abs_rpow hr).map_average_le (f := fun x => f x - c) hg.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => mem_univ _))
      (hf.sub (integrable_const c)) hfr
  rw [average_sub_const' hν hf] at hj
  simpa only [average_eq, smul_eq_mul, Function.comp_apply] using hj

/-- Jensen for the average -/
theorem ofReal_abs_average_rpow_le {τ : ℝ} (hτ : 0 ≤ τ) {r : ℝ} (hr : 1 ≤ r)
    {P : Set (Vec d)} (_hP : MeasurableSet P) {f : Vec d → ℝ}
    (hf : ContinuousOn f (cubeSurface τ)) :
    ENNReal.ofReal (|⨍ x in P, f x ∂surfaceMeasure τ| ^ r) ≤
      (surfaceMeasure τ P)⁻¹ * ∫⁻ x in P, ENNReal.ofReal (|f x| ^ r) ∂surfaceMeasure τ := by
  let := seedSurfaceMeasure_finite (d := d) τ
  have hr0 : 0 ≤ r := by linarith only [hr]
  by_cases h0 : surfaceMeasure τ P = 0
  · have : (surfaceMeasure τ).restrict P = 0 := Measure.restrict_eq_zero.mpr h0
    rw [this]
    simp only [average_zero_measure, abs_zero]
    rw [Real.zero_rpow (by linarith only [hr])]
    simp
  have hne : (surfaceMeasure τ).restrict P ≠ 0 := fun h => h0 (Measure.restrict_eq_zero.mp h)
  have hfi := (integrable_of_continuousOn hτ hf).restrict (s := P)
  have hfr : Integrable (fun x => |f x - 0| ^ r) ((surfaceMeasure τ).restrict P) := by
    simp only [sub_zero]
    exact (integrable_of_continuousOn hτ (hf.abs.rpow_const (fun _ _ => Or.inr hr0))).restrict
  have hj := abs_rpow_sub_average_le hne hr hfi hfr
  simp only [sub_zero, Measure.real, Measure.restrict_apply_univ] at hj
  have hnn : 0 ≤ᵐ[(surfaceMeasure τ).restrict P] fun x => |f x| ^ r :=
    Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hmp : 0 < (surfaceMeasure τ P).toReal :=
    ENNReal.toReal_pos h0 (measure_ne_top _ _)
  calc
    _ ≤ ENNReal.ofReal ((surfaceMeasure τ P).toReal⁻¹ *
        ∫ x, |f x| ^ r ∂(surfaceMeasure τ).restrict P) := ENNReal.ofReal_le_ofReal hj
    _ = _ := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hmp.le), ENNReal.ofReal_inv_of_pos hmp,
        ENNReal.ofReal_toReal (measure_ne_top _ _),
        ofReal_integral_eq_lintegral_ofReal (by simpa only [sub_zero] using hfr) hnn]

/-- Jensen for the difference of two averages -/
theorem ofReal_abs_average_sub_rpow_le {τ : ℝ} (hτ : 0 ≤ τ) {r : ℝ} (hr : 1 ≤ r)
    {P Q : Set (Vec d)} (hP : MeasurableSet P) (hPs : P ⊆ cubeSurface τ)
    (hP0 : 0 < surfaceMeasure τ P) (hQ : MeasurableSet Q) (hQs : Q ⊆ cubeSurface τ)
    (hQ0 : 0 < surfaceMeasure τ Q) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) :
    ENNReal.ofReal (|(⨍ x in P, f x ∂surfaceMeasure τ) - ⨍ y in Q, f y ∂surfaceMeasure τ| ^ r) ≤
      (surfaceMeasure τ P * surfaceMeasure τ Q)⁻¹ *
        ∫⁻ p in P ×ˢ Q, ENNReal.ofReal (|f p.1 - f p.2| ^ r)
          ∂((surfaceMeasure τ).prod (surfaceMeasure τ)) := by
  let := seedSurfaceMeasure_finite (d := d) τ
  set a := (surfaceMeasure τ).restrict P with ha
  set b := (surfaceMeasure τ).restrict Q with hb
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hane : a ≠ 0 := fun h => hP0.ne' (Measure.restrict_eq_zero.mp h)
  have hbne : b ≠ 0 := fun h => hQ0.ne' (Measure.restrict_eq_zero.mp h)
  have hmP : 0 < (surfaceMeasure τ P).toReal := ENNReal.toReal_pos hP0.ne' (measure_ne_top _ _)
  have hmQ : 0 < (surfaceMeasure τ Q).toReal := ENNReal.toReal_pos hQ0.ne' (measure_ne_top _ _)
  have haU : a.real univ = (surfaceMeasure τ P).toReal := by
    simp [ha, Measure.real]
  have hbU : b.real univ = (surfaceMeasure τ Q).toReal := by
    simp [hb, Measure.real]
  have hfint := integrable_of_continuousOn hτ hf
  have hpow : ∀ c : ℝ, Integrable (fun x => |f x - c| ^ r) (surfaceMeasure τ) := fun c =>
    integrable_of_continuousOn hτ
      ((hf.sub continuousOn_const).abs.rpow_const (fun _ _ => Or.inr hr0))
  have hFc : ContinuousOn (fun p : Vec d × Vec d => |f p.1 - f p.2| ^ r)
      (cubeSurface τ ×ˢ cubeSurface τ) := by
    have hx : ContinuousOn (fun p : Vec d × Vec d => f p.1) (cubeSurface τ ×ˢ cubeSurface τ) :=
      hf.comp continuousOn_fst (fun _ hp => hp.1)
    have hy : ContinuousOn (fun p : Vec d × Vec d => f p.2) (cubeSurface τ ×ˢ cubeSurface τ) :=
      hf.comp continuousOn_snd (fun _ hp => hp.2)
    exact (hx.sub hy).abs.rpow_const (fun _ _ => Or.inr hr0)
  have hpair : Integrable (fun p : Vec d × Vec d => |f p.1 - f p.2| ^ r) (a.prod b) := by
    have hcompact := (isCompact_cubeSurface (d := d) τ).prod (isCompact_cubeSurface (d := d) τ)
    have hi := hFc.integrableOn_compact (μ := a.prod b) hcompact
    apply hi.integrable_of_ae_notMem_eq_zero
    have hmem : ∀ᵐ p ∂a.prod b, p ∈ cubeSurface τ ×ˢ cubeSurface τ := by
      apply (Measure.ae_prod_mem_iff_ae_ae_mem hcompact.isClosed.measurableSet).mpr
      filter_upwards [ae_restrict_mem hP] with x hx
      filter_upwards [ae_restrict_mem hQ] with y hy
      exact ⟨hPs hx, hQs hy⟩
    filter_upwards [hmem] with p hp
    exact fun hn => (hn hp).elim
  have hmono : (∫ x, |f x - ⨍ y, f y ∂b| ^ r ∂a) ≤
      ∫ x, (b.real univ)⁻¹ * ∫ y, |f x - f y| ^ r ∂b ∂a := by
    apply integral_mono_ae (hpow _).restrict (hpair.integral_prod_left.const_mul _)
    filter_upwards with x
    have hj := abs_rpow_sub_average_le (ν := b) hbne (c := f x) hr hfint.restrict
      (hpow _).restrict
    simpa only [abs_sub_comm, Real.rpow_natCast] using hj
  have hreal : |(⨍ x, f x ∂a) - ⨍ y, f y ∂b| ^ r ≤
      (∫ x, ∫ y, |f x - f y| ^ r ∂b ∂a) / ((surfaceMeasure τ P).toReal *
        (surfaceMeasure τ Q).toReal) := by
    have h1 := abs_rpow_sub_average_le (ν := a) hane (c := ⨍ y, f y ∂b) hr hfint.restrict
      (hpow _).restrict
    rw [haU] at h1
    rw [hbU] at hmono
    have h2 : (surfaceMeasure τ P).toReal⁻¹ *
        ∫ x, |f x - ⨍ y, f y ∂b| ^ r ∂a ≤ (surfaceMeasure τ P).toReal⁻¹ *
        ∫ x, (surfaceMeasure τ Q).toReal⁻¹ * ∫ y, |f x - f y| ^ r ∂b ∂a :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hmP.le)
    rw [integral_const_mul] at h2
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := by field_simp
  have hnonneg : 0 ≤ᵐ[a.prod b] fun p : Vec d × Vec d => |f p.1 - f p.2| ^ r :=
    Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hprod : a.prod b = ((surfaceMeasure τ).prod (surfaceMeasure τ)).restrict (P ×ˢ Q) := by
    rw [ha, hb, Measure.prod_restrict]
  calc
    _ ≤ ENNReal.ofReal ((∫ x, ∫ y, |f x - f y| ^ r ∂b ∂a) /
        ((surfaceMeasure τ P).toReal * (surfaceMeasure τ Q).toReal)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (∫⁻ p, ENNReal.ofReal (|f p.1 - f p.2| ^ r) ∂(a.prod b)) /
        (surfaceMeasure τ P * surfaceMeasure τ Q) := by
      rw [ENNReal.ofReal_div_of_pos (mul_pos hmP hmQ), ← integral_prod _ hpair,
        ofReal_integral_eq_lintegral_ofReal hpair hnonneg, ENNReal.ofReal_mul hmP.le,
        ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = _ := by rw [hprod, div_eq_mul_inv, mul_comm]

end CoarseDeGiorgi.WhitneyExt
