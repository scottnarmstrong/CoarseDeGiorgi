module

public import CoarseDeGiorgi.Selection.IntervalCover
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

namespace CoarseDeGiorgi.Selection

open MeasureTheory Set Metric Filter
open scoped ENNReal BigOperators Topology

noncomputable section

/-- Centered maximal average of a nonnegative measure on the radius line. -/
def centeredMaximal (ν : Measure ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_hr : 0 < r), ν (ball τ r) / ENNReal.ofReal (2 * r)

/-- The measure of a moving open interval is lower semicontinuous.
No atomlessness is needed: open balls and inner regularity suffice. -/
theorem lowerSemicontinuous_measure_ball (ν : Measure ℝ) [Measure.InnerRegular ν] (r : ℝ) :
    LowerSemicontinuous (fun τ => ν (ball τ r)) := by
  intro τ c hc
  obtain ⟨K, hKsub, hK, hmass⟩ := isOpen_ball.measurableSet.exists_lt_isCompact hc
  have hKne : K.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, measure_empty] at hmass
    exact not_lt_bot hmass
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hKne
    (continuous_id.dist continuous_const).continuousOn
  have hzball : dist z τ < r := hKsub hz
  have hε : 0 < r - dist z τ := sub_pos.mpr hzball
  filter_upwards [Metric.ball_mem_nhds τ hε] with τ' hτ'
  apply hmass.trans_le
  apply measure_mono
  intro w hw
  change dist w τ' < r
  have hwmax : dist w τ ≤ dist z τ := hmax hw
  have hshift : dist τ τ' < r - dist z τ := by
    change dist τ' τ < r - dist z τ at hτ'
    simpa only [dist_comm] using hτ'
  exact (dist_triangle w τ τ').trans_lt (by linarith)

/-- Measurability of the maximal function is obtained from lower semicontinuity. -/
theorem centeredMaximal_lowerSemicontinuous (ν : Measure ℝ) [Measure.InnerRegular ν] :
    LowerSemicontinuous (centeredMaximal ν) := by
  apply lowerSemicontinuous_biSup
  intro r hr
  exact (ENNReal.continuous_div_const (ENNReal.ofReal (2 * r))
    ((ENNReal.ofReal_pos.mpr (by positivity)).ne')).comp_lowerSemicontinuous
      (lowerSemicontinuous_measure_ball ν r) (fun _ _ h => by dsimp; gcongr)


/-- Compact bad sets have the sharp finite-cover constant three. -/
theorem centeredMaximal_compact_bound (ν : Measure ℝ) {Γ : ℝ} (hΓ : 0 < Γ)
    {K : Set ℝ} (hK : IsCompact K) (hbad : K ⊆ {τ | ENNReal.ofReal Γ < centeredMaximal ν τ}) :
    volume K ≤ 3 * ν univ / ENNReal.ofReal Γ := by
  classical
  have hwitness (τ : K) : ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal Γ < ν (ball τ r) / ENNReal.ofReal (2 * r) := by
    have hτ := hbad τ.property
    change ENNReal.ofReal Γ < centeredMaximal ν τ at hτ
    simpa only [centeredMaximal, lt_iSup_iff, exists_prop] using hτ
  choose r hr havg using hwitness
  have hcover : K ⊆ ⋃ τ : K, ball (τ : ℝ) (r τ) := by
    intro τ hτ
    exact mem_iUnion.mpr ⟨⟨τ, hτ⟩, mem_ball_self (hr _)⟩
  obtain ⟨s, hscover⟩ := hK.elim_finite_subcover _ (fun _ => isOpen_ball) hcover
  obtain ⟨u, hus, hdis, hucover⟩ := exists_disjoint_intervals_covering_three s
    (fun τ : K => (τ : ℝ)) r (fun τ _ => hr τ)
  have hsub : K ⊆ ⋃ τ ∈ u, ball (τ : ℝ) (3 * r τ) := by
    intro τ hτ
    obtain ⟨a, has, hτa⟩ := mem_iUnion₂.mp (hscover hτ)
    obtain ⟨b, hb, hab⟩ := hucover a has
    exact mem_iUnion₂.mpr ⟨b, hb, hab hτa⟩
  have hvol (τ : K) : volume (ball (τ : ℝ) (r τ)) = ENNReal.ofReal (2 * r τ) := by
    rw [Real.ball_eq_Ioo, Real.volume_Ioo]
    congr 1; ring
  have hmass (τ : K) : ENNReal.ofReal Γ * volume (ball (τ : ℝ) (r τ)) ≤ ν (ball τ (r τ)) := by
    rw [hvol]
    exact (ENNReal.le_div_iff_mul_le (Or.inl ((ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (hr τ))).ne'))
      (Or.inl ENNReal.ofReal_ne_top)).mp (havg τ).le
  have hsum : ENNReal.ofReal Γ * ∑ τ ∈ u, volume (ball (τ : ℝ) (r τ)) ≤ ν univ := by
    calc
      _ = ∑ τ ∈ u, ENNReal.ofReal Γ * volume (ball (τ : ℝ) (r τ)) := Finset.mul_sum _ _ _
      _ ≤ ∑ τ ∈ u, ν (ball (τ : ℝ) (r τ)) := Finset.sum_le_sum (fun τ _ => hmass τ)
      _ = ν (⋃ τ ∈ u, ball (τ : ℝ) (r τ)) := by
        rw [measure_biUnion_finset hdis (fun _ _ => isOpen_ball.measurableSet)]
      _ ≤ ν univ := measure_mono (subset_univ _)
  have hsum' : (∑ τ ∈ u, volume (ball (τ : ℝ) (r τ))) ≤ ν univ / ENNReal.ofReal Γ := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl ((ENNReal.ofReal_pos.mpr hΓ).ne'))
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using hsum
  calc
    volume K ≤ volume (⋃ τ ∈ u, ball (τ : ℝ) (3 * r τ)) := measure_mono hsub
    _ ≤ ∑ τ ∈ u, volume (ball (τ : ℝ) (3 * r τ)) := measure_biUnion_finset_le _ _
    _ = 3 * ∑ τ ∈ u, volume (ball (τ : ℝ) (r τ)) := by
      simp_rw [volume_ball_three]
      rw [Finset.mul_sum]
    _ ≤ 3 * (ν univ / ENNReal.ofReal Γ) := by gcongr
    _ = _ := by rw [mul_div_assoc]

/-- Weak (1,1) for the centered maximal function, with constant exactly three. -/
theorem centeredMaximal_weak_bound (ν : Measure ℝ) [Measure.InnerRegular ν]
    {Γ : ℝ} (hΓ : 0 < Γ) :
    volume {τ | ENNReal.ofReal Γ < centeredMaximal ν τ} ≤ 3 * ν univ / ENNReal.ofReal Γ := by
  have hopen := (centeredMaximal_lowerSemicontinuous ν).isOpen_preimage (ENNReal.ofReal Γ)
  change volume (centeredMaximal ν ⁻¹' Ioi (ENNReal.ofReal Γ)) ≤ _
  rw [hopen.measurableSet.measure_eq_iSup_isCompact volume]
  exact iSup_le (fun K => iSup_le (fun hsub => iSup_le (fun hK =>
    centeredMaximal_compact_bound ν hΓ hK hsub)))


end

end CoarseDeGiorgi.Selection
