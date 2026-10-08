module

public import Mathlib.Analysis.Calculus.MeanValue
public import CoarseDeGiorgi.Whitney.Extension.Basic

/-! # Gluing a uniform local bound into a global Lipschitz bound -/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt
open Set Filter
open scoped Topology
noncomputable section

/-- Near a point, a finite closed cover uses only pieces containing that point. -/
theorem glueFiniteClosedCover_local_bound {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (patch : ι → Set X) (U : Set X) (F : X → ℝ) (K : ℝ)
    (D : X → X → ℝ) (hc : ∀ i ∈ s, IsClosed (patch i))
    (hcover : ∀ y ∈ U, ∃ i ∈ s, y ∈ patch i)
    (hpiece : ∀ i ∈ s, ∀ x ∈ patch i, ∀ y ∈ patch i, |F y - F x| ≤ K * D y x)
    (x : X) : ∀ᶠ y in 𝓝[U] x, |F y - F x| ≤ K * D y x := by
  classical
  have havoid : ∀ i ∈ s, ∀ᶠ y in 𝓝 x, y ∈ patch i → x ∈ patch i := by
    intro i hi
    by_cases hx : x ∈ patch i
    · exact Eventually.of_forall (fun _ _ => hx)
    · filter_upwards [(hc i hi).isOpen_compl.mem_nhds hx] with y hy
      exact fun hp => False.elim (hy hp)
  have hall : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, y ∈ patch i → x ∈ patch i :=
    (s.eventually_all).mpr havoid
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyU
  obtain ⟨i, hi, hyp⟩ := hcover y hyU
  exact hpiece i hi x (hy i hi hyp) y hyp

/-- A uniform local anchored bound glues along a closed interval, including corners. -/
theorem glueInterval_bound_of_local {a b K : ℝ} (hab : a ≤ b) (F : ℝ → ℝ)
    (hf : ContinuousOn F (Icc a b))
    (hloc : ∀ x ∈ Ico a b, ∀ᶠ z in 𝓝[>] x, |F z - F x| ≤ K * |z - x|) :
    |F b - F a| ≤ K * (b - a) := by
  let g : ℝ → ℝ := fun x => |F x - F a|
  have hg : ContinuousOn g (Icc a b) := (hf.sub continuousOn_const).abs
  have ha : g a ≤ K * (a - a) := by simp [g]
  have hB : ContinuousOn (fun x : ℝ => K * (x - a)) (Icc a b) := by fun_prop
  have hder : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun t : ℝ => K * (t - a)) K (Ici x) x := by
    intro x _
    simpa using (((hasDerivAt_id x).sub_const a).const_mul K).hasDerivWithinAt
  have hslope : ∀ x ∈ Ico a b, ∀ r : ℝ, K < r → ∃ᶠ z in 𝓝[>] x, slope g x z < r := by
    intro x hx r hr
    apply Filter.Eventually.frequently
    filter_upwards [hloc x hx, self_mem_nhdsWithin] with z hz hzx
    have hpos : 0 < z - x := sub_pos.mpr hzx
    have hd : g z - g x ≤ |F z - F x| := by
      have ht := abs_add_le (F z - F x) (F x - F a)
      have he : F z - F x + (F x - F a) = F z - F a := by ring
      rw [he] at ht
      dsimp [g]
      linarith only [ht]
    have hle : slope g x z ≤ K := by
      rw [slope_def_field]
      apply (div_le_iff₀ hpos).mpr
      rw [abs_of_pos hpos] at hz
      exact hd.trans hz
    exact hle.trans_lt hr
  exact image_le_of_liminf_slope_right_le_deriv_boundary hg ha hB hder hslope ⟨hab, le_rfl⟩


section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A uniform anchored bound implies continuity before the interval argument. -/
theorem glueContinuous_of_local_bound (F : E → ℝ) (K : ℝ)
    (hloc : ∀ x, ∀ᶠ y in 𝓝 x, |F y - F x| ≤ K * ‖y - x‖) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Tendsto F (𝓝 x) (𝓝 (F x))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlim : Tendsto (fun y : E => K * ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : E => K * ‖y - x‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using (hc.continuousAt (x := x)).tendsto
  have he := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hloc x, he] with y hy hyε
  simpa only [Real.dist_eq] using hy.trans_lt hyε

/-- Straight-line gluing does not require differentiability at the joins. -/
theorem glueGlobal_bound_of_local (F : E → ℝ) (K : ℝ)
    (hloc : ∀ x, ∀ᶠ y in 𝓝 x, |F y - F x| ≤ K * ‖y - x‖) (x y : E) :
    |F y - F x| ≤ K * ‖y - x‖ := by
  let line : ℝ → E := fun t => x + t • (y - x)
  have hline : Continuous line := by dsimp [line]; fun_prop
  have hF := glueContinuous_of_local_bound F K hloc
  have hd (t z : ℝ) : ‖line z - line t‖ = |z - t| * ‖y - x‖ := by
    have he : line z - line t = (z - t) • (y - x) := by
      dsimp [line]
      rw [sub_smul]
      abel
    rw [he, norm_smul, Real.norm_eq_abs]
  have hl : ∀ t ∈ Ico (0 : ℝ) 1, ∀ᶠ z in 𝓝[>] t,
      |F (line z) - F (line t)| ≤ (K * ‖y - x‖) * |z - t| := by
    intro t _
    have ht : ∀ᶠ z in 𝓝[>] t, |F (line z) - F (line t)| ≤ K * ‖line z - line t‖ :=
      (hline.continuousAt.tendsto.eventually (hloc (line t))).filter_mono nhdsWithin_le_nhds
    filter_upwards [ht] with z hz
    rw [hd] at hz
    convert hz using 1
    ring
  have hb := glueInterval_bound_of_local (by norm_num : (0 : ℝ) ≤ 1) (F ∘ line)
    (hF.comp hline).continuousOn hl
  have hend : x + (y - x) = y := by abel
  simpa only [Function.comp_apply, line, zero_smul, add_zero, one_smul, sub_add_cancel,
    sub_zero, mul_one, hend] using hb


end

end
end CoarseDeGiorgi.WhitneyExt
