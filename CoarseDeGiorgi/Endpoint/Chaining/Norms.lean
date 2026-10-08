module

public import CoarseDeGiorgi.Endpoint.Chaining.Geometry
public import CoarseDeGiorgi.Harnack.Iterations.NormalizedMomentOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Essential values, finite coverings, and volume corrections used in chaining. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint
open Homogenization MeasureTheory Filter
open scoped BigOperators ENNReal

/-- One member of a finite cover has infimum no greater than that on the covered set. -/
theorem exists_cover_inf_le {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : Set (Vec d)) (Q : ι → Set (Vec d)) (u : Vec d → ℝ)
    (hcover : V ⊆ ⋃ i, Q i) :
    ∃ i, nonnegativeEssInf (Q i) u ≤ nonnegativeEssInf V u := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => nonnegativeEssInf (Q i) u)
  refine ⟨i, ?_⟩
  rw [hi]
  refine le_essInf_of_ae_le _ ?_ (by isBoundedDefault)
  apply ae_restrict_of_ae_restrict_of_subset hcover
  apply (ae_restrict_iUnion_iff Q _).mpr
  intro j
  exact (ae_essInf_le (f := fun x => ENNReal.ofReal (u x))
    (μ := volume.restrict (Q j))).mono (fun x hx => (iInf_le _ j).trans hx)

theorem eLpNorm'_eq_volume_mul_moment {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ)
    {b : ℝ} (hb : 0 < b) (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤) :
    eLpNorm' u b (volume.restrict V) =
      (volume V) ^ (1 / b) * normalizedLpMoment b hb V u := by
  rw [Harnack.Iterations.normalizedLpMoment_eq_eLpNorm' V u hb,
    Measure.restrict_apply_univ, ← mul_assoc,
    ← ENNReal.rpow_add (1 / b) (-1 / b) hV0 hVtop]
  rw [show (1 / b : ℝ) + -1 / b = 0 by ring, ENNReal.rpow_zero, one_mul]

/-- A fixed positive-volume overlap controls the infimum of either adjacent cube. -/
theorem inf_le_moment_of_overlap {d : ℕ} (E V W : Set (Vec d)) (u : Vec d → ℝ)
    {b : ℝ} (hb : 0 < b) (hEV : E ⊆ V) (hEW : E ⊆ W)
    (hE0 : volume E ≠ 0) (hEtop : volume E ≠ ⊤)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ⊤) :
    nonnegativeEssInf W u ≤
      ((volume E) ^ (-1 / b) * (volume V) ^ (1 / b)) *
        normalizedLpMoment b hb V u := by
  let m := nonnegativeEssInf W u
  have hlower : ∀ᵐ x ∂(volume.restrict E), m ≤ ENNReal.ofReal |u x| := by
    have h := ae_restrict_of_ae_restrict_of_subset hEW
      (ae_essInf_le (f := fun x => ENNReal.ofReal (u x)) (μ := volume.restrict W))
    exact h.mono (fun x hx => hx.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
  have hp : m ^ b * volume E ≤ ∫⁻ x in V, (ENNReal.ofReal |u x|) ^ b := by
    calc
      _ = ∫⁻ x in E, m ^ b := by simp only [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x in E, (ENNReal.ofReal |u x|) ^ b :=
        lintegral_mono_ae (hlower.mono (fun _ hx => ENNReal.rpow_le_rpow hx hb.le))
      _ ≤ _ := lintegral_mono_set hEV
  have hp' := ENNReal.rpow_le_rpow hp (by positivity : 0 ≤ 1 / b)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / b),
    ← ENNReal.rpow_mul, mul_one_div_cancel hb.ne', ENNReal.rpow_one] at hp'
  have hraw : m * (volume E) ^ (1 / b) ≤ eLpNorm' u b (volume.restrict V) := by
    simpa only [eLpNorm'_eq_lintegral_enorm, Real.enorm_eq_ofReal_abs] using hp'
  calc
    m = (volume E) ^ (-1 / b) * (m * (volume E) ^ (1 / b)) := by
      have hcancel : (volume E) ^ (-1 / b) * (volume E) ^ (1 / b) = 1 := by
        rw [← ENNReal.rpow_add (-1 / b) (1 / b) hE0 hEtop,
          show (-1 / b : ℝ) + 1 / b = 0 by ring, ENNReal.rpow_zero]
      calc
        m = m * 1 := (mul_one m).symm
        _ = m * ((volume E) ^ (-1 / b) * (volume E) ^ (1 / b)) := by rw [hcancel]
        _ = _ := by ac_rfl
    _ ≤ (volume E) ^ (-1 / b) * eLpNorm' u b (volume.restrict V) :=
      mul_le_mul_of_nonneg_left hraw zero_le
    _ = _ := by rw [eLpNorm'_eq_volume_mul_moment V u hb hV0 hVtop, mul_assoc]

/-- Overlapping sets compare their essential infimum and essential supremum. -/
theorem inf_le_sup_of_overlap {d : ℕ} (E V W : Set (Vec d)) (u : Vec d → ℝ)
    (hEV : E ⊆ V) (hEW : E ⊆ W) (hE0 : volume E ≠ 0)
    (hu : AEStronglyMeasurable u (volume.restrict V)) :
    nonnegativeEssInf W u ≤ eLpNorm u ⊤ (volume.restrict V) := by
  have hi := ae_restrict_of_ae_restrict_of_subset hEW
    (ae_essInf_le (f := fun x => ENNReal.ofReal (u x)) (μ := volume.restrict W))
  have hs := ae_restrict_of_ae_restrict_of_subset hEV
    (ae_le_eLpNormEssSup (f := u) (μ := volume.restrict V))
  have hμ : volume.restrict E ≠ 0 := by
    intro h
    have hh := congrArg (fun μ : Measure (Vec d) => μ Set.univ) h
    exact hE0 (by simpa using hh)
  let : NeZero (volume.restrict E) := ⟨hμ⟩
  obtain ⟨x, hx, hy⟩ := (hi.and hs).exists
  calc
    _ ≤ ENNReal.ofReal (u x) := hx
    _ ≤ ‖u x‖ₑ := by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ eLpNormEssSup u (volume.restrict V) := hy
    _ = _ := (eLpNorm_exponent_top hu).symm

/-- A finite cover turns uniform local moments into an unnormalized global norm. -/
theorem eLpNorm'_cover_le {d : ℕ} {ι : Type*} [Fintype ι]
    (V : Set (Vec d)) (Q : ι → Set (Vec d)) (u : Vec d → ℝ)
    {b : ℝ} (hb : 0 < b) (hcover : V ⊆ ⋃ i, Q i) (M : ℝ≥0∞)
    (hlocal : ∀ i, eLpNorm' u b (volume.restrict (Q i)) ≤ M) :
    eLpNorm' u b (volume.restrict V) ≤
      (Fintype.card ι : ℝ≥0∞) ^ (1 / b) * M := by
  have hlocal' (i : ι) : ∫⁻ x in Q i, ‖u x‖ₑ ^ b ≤ M ^ b := by
    have h := ENNReal.rpow_le_rpow (hlocal i) hb.le
    rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul,
      one_div_mul_cancel hb.ne', ENNReal.rpow_one] at h
    exact h
  have hsum : ∫⁻ x in V, ‖u x‖ₑ ^ b ≤ (Fintype.card ι : ℝ≥0∞) * M ^ b := calc
    _ ≤ ∫⁻ x in ⋃ i, Q i, ‖u x‖ₑ ^ b := lintegral_mono_set hcover
    _ ≤ ∑' i, ∫⁻ x in Q i, ‖u x‖ₑ ^ b := lintegral_iUnion_le Q _
    _ = ∑ i, ∫⁻ x in Q i, ‖u x‖ₑ ^ b := tsum_fintype _
    _ ≤ ∑ _i : ι, M ^ b := Finset.sum_le_sum (fun i _ => hlocal' i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h := ENNReal.rpow_le_rpow hsum (by positivity : 0 ≤ 1 / b)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / b),
    ← ENNReal.rpow_mul, mul_one_div_cancel hb.ne', ENNReal.rpow_one] at h
  exact h

/-- Supremum bounds glue across a finite cover. -/
theorem eLpNorm_top_cover_le {d : ℕ} {ι : Type*} [Fintype ι]
    (V : Set (Vec d)) (Q : ι → Set (Vec d)) (u : Vec d → ℝ)
    (huV : AEStronglyMeasurable u (volume.restrict V))
    (huQ : ∀ i, AEStronglyMeasurable u (volume.restrict (Q i)))
    (hcover : V ⊆ ⋃ i, Q i) (M : ℝ≥0∞)
    (hlocal : ∀ i, eLpNorm u ⊤ (volume.restrict (Q i)) ≤ M) :
    eLpNorm u ⊤ (volume.restrict V) ≤ M := by
  rw [eLpNorm_exponent_top huV]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  apply ae_restrict_of_ae_restrict_of_subset hcover
  apply (ae_restrict_iUnion_iff Q _).mpr
  intro i
  have h := ae_le_eLpNormEssSup (f := u) (μ := volume.restrict (Q i))
  rw [← eLpNorm_exponent_top (huQ i)] at h
  exact h.mono (fun _ hx => hx.trans (hlocal i))

/-- Iterate a multiplicative comparison along the fixed grid path. -/
theorem chaining_inf_le {d N : ℕ} (I : (Fin d → Fin (2 * N + 1)) → ℝ≥0∞)
    (B : ℝ≥0∞) (hstep : ∀ m n, (∀ i, |chainingCenter N m i -
      chainingCenter N n i| ≤ 1 / 81) → I n ≤ B * I m)
    (m n : Fin d → Fin (2 * N + 1)) : I n ≤ B ^ (2 * N) * I m := by
  have h (k : ℕ) : I (chainingPath m n k) ≤ B ^ k * I m := by
    induction k with
    | zero => simp only [chainingPath_zero, pow_zero, one_mul, le_refl]
    | succ k hk =>
      calc
        _ ≤ B * I (chainingPath m n k) :=
          hstep _ _ (chainingPath_step m n k)
        _ ≤ B * (B ^ k * I m) := mul_le_mul_of_nonneg_left hk zero_le
        _ = B ^ (k + 1) * I m := by rw [pow_succ]; ac_rfl
  simpa only [chainingPath_end] using h (2 * N)

end CoarseDeGiorgi.Endpoint
