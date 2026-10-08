import CoarseDeGiorgi.Weighted.Testing
import CoarseDeGiorgi.Weighted.TestingStep

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Testing with a smooth nondecreasing scalar step discards a nonnegative
quadratic term and leaves the truncated flux inequality. -/
theorem IsWeightedSubsolution.testing_gStep (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.IsWeightedSubsolution a V u G)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ V) (hnonneg : ∀ x, 0 ≤ φ x)
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x in V, gStep c δ (u x) * vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ≤ 0 := by
  obtain ⟨L, hL⟩ := testing_gStep_deriv_bounded c hδ
  have hχ : ∀ t, |gStep c δ t| ≤ (1 : ℝ≥0) := fun t => by
    rw [abs_of_nonneg (gStep_nonneg c δ t)]
    exact gStep_le_one c δ t
  have hg := MemH1a.cutoff_comp hV hne ha hu.1 hφ hc hs (gStep_contDiff c δ) hL hχ
  have htest := IsWeightedSubsolution.testing hV hne ha hu hg
    (Eventually.of_forall fun x => mul_nonneg (hnonneg x) (gStep_nonneg c δ (u x)))
  let p : Vec d → ℝ := fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))
  let q : Vec d → ℝ := fun x => vecDot (G x) (matVecMul (a x) (G x))
  have hpI : IntegrableOn p V := (pairing_integrable_and_bound ha
    (smoothGrad_aestronglyMeasurable hV.isOpen hφ.contDiffOn) hu.1.2.1
    (isSmoothCore_of_supported ha hφ hc).2.2
    (MemH1a.energy_lt_top hV.isOpen ha hu.1)).1
  have hfirstI : IntegrableOn (fun x => gStep c δ (u x) * p x) V :=
    hpI.bdd_mul ((gStep_continuous c δ).comp_aestronglyMeasurable hu.1.1)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hχ (u x))
  have hpair : (fun x => vecDot
      (φ x • (deriv (gStep c δ) (u x) • G x) + gStep c δ (u x) • smoothGrad φ x)
      (matVecMul (a x) (G x))) =
      (fun x => φ x * deriv (gStep c δ) (u x) * q x + gStep c δ (u x) * p x) := by
    funext x
    simp only [vecDot_add_left, vecDot_smul_left, p, q, mul_assoc]
  have hsecondI : IntegrableOn (fun x => φ x * deriv (gStep c δ) (u x) * q x) V := by
    rw [hpair] at htest
    convert htest.1.sub hfirstI using 1
    funext x
    simp only [Pi.sub_apply, add_sub_cancel_right]
  have hsecond : 0 ≤ ∫ x in V, φ x * deriv (gStep c δ) (u x) * q x := by
    apply integral_nonneg_of_ae
    filter_upwards [quadratic_nonneg ha G] with x hx
    exact mul_nonneg (mul_nonneg (hnonneg x) (testing_gStep_deriv_nonneg c hδ (u x))) hx
  rw [hpair, integral_add hsecondI hfirstI] at htest
  linarith only [htest.2, hsecond]

/-- Positive parts above any level preserve the weighted subsolution predicate,
with the exact strict-level indicator gradient (`l.weighted.testing`). -/
theorem IsWeightedSubsolution.max_sub_const (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.IsWeightedSubsolution a V u G) (c : ℝ) :
    CoarseDeGiorgi.IsWeightedSubsolution a V (fun x => max (u x - c) 0)
      ({x | c < u x}.indicator G) := by
  have hw := MemH1a.max_sub_const hV hne ha hu.1 c
  refine ⟨hw, ?_⟩
  intro φ hφ hc hs hnonneg
  have hφcore := isSmoothCore_of_supported ha hφ hc
  have hφM := smoothGrad_aestronglyMeasurable hV.isOpen hφ.contDiffOn
  have hp := pairing_integrable_and_bound ha hφM hu.1.2.1 hφcore.2.2
    (MemH1a.energy_lt_top hV.isOpen ha hu.1)
  refine ⟨(pairing_integrable_and_bound ha hφM hw.2.1 hφcore.2.2
    (MemH1a.energy_lt_top hV.isOpen ha hw)).1, ?_⟩
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδpos : ∀ n, 0 < δ n := by intro n; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let p : Vec d → ℝ := fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))
  have hlim := tendsto_integral_of_dominated_convergence (fun x => |p x|)
    (F := fun n x => gStep c (δ n) (u x) * p x)
    (f := fun x => (if c < u x then 1 else 0) * p x)
    (fun n => ((gStep_continuous c (δ n)).comp_aestronglyMeasurable hu.1.1).mul hp.1.1)
    hp.1.abs (fun n => ?_) ?_
  · have hbound := le_of_tendsto hlim (Eventually.of_forall fun n =>
      IsWeightedSubsolution.testing_gStep hV hne ha hu hφ hc hs hnonneg c (hδpos n))
    convert hbound using 1
    congr 1
    funext x
    by_cases hx : c < u x <;> simp [p, hx, matVecMul, vecDot]
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gStep_nonneg c (δ n) (u x))]
    exact (mul_le_mul_of_nonneg_right (gStep_le_one c (δ n) (u x)) (abs_nonneg _)).trans_eq
      (one_mul _)
  · filter_upwards with x
    exact (tendsto_gStep (c := c) hδpos hδ (u x)).mul_const (p x)

/-- The positive part of a weighted subsolution is a weighted subsolution. -/
theorem IsWeightedSubsolution.posPart (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.IsWeightedSubsolution a V u G) :
    CoarseDeGiorgi.IsWeightedSubsolution a V (fun x => max (u x) 0)
      ({x | 0 < u x}.indicator G) := by
  simpa only [sub_zero] using IsWeightedSubsolution.max_sub_const hV hne ha hu 0



end CoarseDeGiorgi.Weighted
