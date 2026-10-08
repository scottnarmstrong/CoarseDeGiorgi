import CoarseDeGiorgi.Whitney.LiftCountable

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators
noncomputable section
variable {d : ℕ} {V : Set (Vec d)}

/-- A global L¹ limit equals any eventually stationary local value. -/
lemma lift_limit_eq_on_set {A : Set (Vec d)} (hA : MeasurableSet A) (hAV : A ⊆ V)
    {u : ℕ → Vec d → ℝ} {w f : Vec d → ℝ}
    (hL : Tendsto (fun n => eLpNorm (u n - w) 1 (volume.restrict V)) atTop (𝓝 0))
    (he : ∀ᶠ n in atTop, ∀ x ∈ A, u n x = f x) :
    w =ᵐ[volume.restrict A] f := by
  have hLW : Tendsto (fun n => eLpNorm (u n - w) 1 (volume.restrict A)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL (fun _ => bot_le)
      (fun n => eLpNorm_mono_measure _ (Measure.restrict_mono hAV le_rfl))
  have hLF : Tendsto (fun n => eLpNorm (u n - f) 1 (volume.restrict A)) atTop (𝓝 0) := by
    apply tendsto_congr' _ |>.mpr tendsto_const_nhds
    filter_upwards [he] with n hn
    apply eLpNorm_eq_zero_of_ae_zero
    filter_upwards [ae_restrict_mem hA] with x hx
    exact sub_eq_zero.mpr (hn x hx)
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by simp) hLW)
    (tendstoInMeasure_of_tendsto_eLpNorm (by simp) hLF)

/-- Disjoint partial sums eventually contain exactly the correction of a fixed cell. -/
lemma lift_partial_eq_on_cell (U : ℕ → Set (Vec d)) (u : ℕ → Vec d → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hsupp : ∀ k x, x ∉ U k → u k x = 0) (k : ℕ) :
    ∀ᶠ n in atTop, ∀ x ∈ U k, (∑ j ∈ Finset.range n, u j) x = u k x := by
  filter_upwards [eventually_gt_atTop k] with n hn
  intro x hx
  rw [Finset.sum_apply]
  apply Finset.sum_eq_single k
  · intro j _ hj
    exact hsupp j x (fun hy => (disjoint_left.mp (hdisj hj)) hy hx)
  · intro hk
    exact False.elim (hk (Finset.mem_range.mpr hn))

/-- The countable correction's L¹ limit agrees with every cell correction. -/
lemma lift_limit_eq_on_cell (U : ℕ → Set (Vec d)) (u : ℕ → Vec d → ℝ)
    (hU : ∀ k, MeasurableSet (U k)) (hUV : ∀ k, U k ⊆ V) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hsupp : ∀ k x, x ∉ U k → u k x = 0) {w : Vec d → ℝ}
    (hL : Tendsto (fun n => eLpNorm ((∑ k ∈ Finset.range n, u k) - w) 1
      (volume.restrict V)) atTop (𝓝 0)) (k : ℕ) :
    w =ᵐ[volume.restrict (U k)] u k :=
  lift_limit_eq_on_set (hU k) (hUV k) hL (lift_partial_eq_on_cell U u hdisj hsupp k)

/-- Away from all cells the countable correction is zero, in particular on the inner cube. -/
lemma lift_limit_zero_on_set {A : Set (Vec d)} (hA : MeasurableSet A) (hAV : A ⊆ V)
    (u : ℕ → Vec d → ℝ) (hz : ∀ k x, x ∈ A → u k x = 0) {w : Vec d → ℝ}
    (hL : Tendsto (fun n => eLpNorm ((∑ k ∈ Finset.range n, u k) - w) 1
      (volume.restrict V)) atTop (𝓝 0)) : w =ᵐ[volume.restrict A] 0 := by
  apply lift_limit_eq_on_set hA hAV hL
  filter_upwards with n
  intro x hx
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun k _ => hz k x hx)

end
end CoarseDeGiorgi.Whitney
