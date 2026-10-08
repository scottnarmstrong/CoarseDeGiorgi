import CoarseDeGiorgi.Endpoint.Capacitary.Geometry
import CoarseDeGiorgi.Whitney.SeedInterpolation

/-! A fixed level-four nodal cutoff for the remote obstacle. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Metric Filter
open CoarseDeGiorgi.Whitney

variable {d : ℕ}

/-- Only finitely many level-four vertices lie within two mesh widths of the remote center. -/
theorem finite_capacitary_nodes :
    {m : Fin d → ℤ | ‖seedNode 4 m - remoteCenter d‖ ≤ (2 / 81 : ℝ)}.Finite := by
  apply (finite_seedNodes_in_ball (d := d) 4 (4 / 9)).subset
  intro m hm
  change ‖seedNode 4 m - remoteCenter d‖ ≤ (2 / 81 : ℝ) at hm
  have h := norm_sub_le_norm_sub_add_norm_sub (seedNode 4 m) (remoteCenter d) 0
  simp only [sub_zero] at h
  have hc := remoteCenter_norm_le (d := d)
  change ‖seedNode 4 m‖ ≤ 4 / 9
  linarith only [h, hm, hc]

/-- The vertices assigned value one for the level-four cutoff. -/
noncomputable def capacitaryNodes (d : ℕ) : Finset (Fin d → ℤ) :=
  finite_capacitary_nodes.toFinset

/-- The finite sum of level-four nodal hats attached to the selected vertices. -/
noncomputable def capacitarySeed (d : ℕ) (x : Vec d) : ℝ :=
  ∑ m ∈ capacitaryNodes d, seedHat 4 m x

theorem mem_capacitaryNodes (m : Fin d → ℤ) :
    m ∈ capacitaryNodes d ↔ ‖seedNode 4 m - remoteCenter d‖ ≤ (2 / 81 : ℝ) := by
  exact Set.Finite.mem_toFinset _

/-- The cutoff agrees with the arbitrary nodal-interpolation API. -/
theorem capacitarySeed_eq_interpolation (x : Vec d) :
    capacitarySeed d x = seedInterpolation 4
      (fun m => if m ∈ capacitaryNodes d then 1 else 0) x := by
  classical
  unfold capacitarySeed seedInterpolation
  rw [tsum_eq_sum (s := capacitaryNodes d)]
  · apply Finset.sum_congr rfl
    intro m hm
    simp only [ite_eq_left hm, one_mul]
  · intro m hm
    simp only [ite_eq_right hm, zero_mul]

/-- The cutoff is identically one on the remote half cube. -/
theorem capacitarySeed_eq_one {x : Vec d} (hx : x ∈ remoteCube d (1 / 2)) :
    capacitarySeed d x = 1 := by
  classical
  have hx' : ‖x - remoteCenter d‖ < (1 / 108 : ℝ) := by
    simpa only [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1 / 2), Metric.mem_ball,
      dist_eq_norm, show (1 / 2 : ℝ) / 54 = 1 / 108 by norm_num] using hx
  rw [capacitarySeed_eq_interpolation]
  unfold seedInterpolation
  calc
    _ = ∑' m : Fin d → ℤ, seedHat 4 m x := by
      apply tsum_congr
      intro m
      by_cases hm : seedHat 4 m x = 0
      · rw [hm, mul_zero]
      · have hdist := norm_sub_lt_of_nodalHat_ne_zero (seedScale_pos 4) hm
        change ‖x - seedNode 4 m‖ < seedScale 4 at hdist
        have hscale : seedScale 4 = (1 / 81 : ℝ) := by norm_num [seedScale]
        rw [hscale, norm_sub_rev] at hdist
        have htri := norm_sub_le_norm_sub_add_norm_sub (seedNode 4 m) x (remoteCenter d)
        have hnode : m ∈ capacitaryNodes d := mem_capacitaryNodes _ |>.mpr (by
          linarith only [htri, hdist, hx'])
        simp only [ite_eq_left hnode, one_mul]
    _ = 1 := tsum_seedHat 4 x

/-- The nodal cutoff vanishes outside a compact subset of the unit cube. -/
theorem capacitarySeed_eq_zero {x : Vec d} (hx : (3 / 81 : ℝ) ≤ ‖x - remoteCenter d‖) :
    capacitarySeed d x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro m hm
  by_contra hn
  have hdist := norm_sub_lt_of_nodalHat_ne_zero (seedScale_pos 4) hn
  change ‖x - seedNode 4 m‖ < seedScale 4 at hdist
  have hscale : seedScale 4 = (1 / 81 : ℝ) := by norm_num [seedScale]
  rw [hscale] at hdist
  have hnode := (mem_capacitaryNodes m).mp hm
  have htri := norm_sub_le_norm_sub_add_norm_sub x (seedNode 4 m) (remoteCenter d)
  linarith only [hx, hdist, hnode, htri]

/-- Positive coordinate projection is nonexpansive for the ambient maximum norm. -/
theorem positivePeak_sub_le (x y : Vec d) :
    |positivePeak x - positivePeak y| ≤ ‖x - y‖ := by
  have hcoord : ‖(fun i => max (x i) 0) - (fun i => max (y i) 0)‖ ≤ ‖x - y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact (show |max (x i) 0 - max (y i) 0| ≤ |x i - y i| from
      abs_max_sub_max_le_abs _ _ _).trans
      (norm_le_pi_norm (x - y) i)
  exact (abs_norm_sub_norm_le _ _).trans hcoord

/-- A level-four nodal hat is Lipschitz with a universal constant. -/
theorem capacitary_seedHat_sub_le (m : Fin d → ℤ) (x y : Vec d) :
    |seedHat 4 m x - seedHat 4 m y| ≤ 162 * ‖x - y‖ := by
  let z := seedNode 4 m
  have hp := positivePeak_sub_le (x - z) (y - z)
  have hn := positivePeak_sub_le (z - x) (z - y)
  rw [sub_sub_sub_cancel_right] at hp
  rw [show z - x - (z - y) = y - x by abel, norm_sub_rev] at hn
  have hs := abs_add_le (positivePeak (x - z) - positivePeak (y - z))
    (positivePeak (z - x) - positivePeak (z - y))
  have hsum : |(positivePeak (x - z) + positivePeak (z - x)) -
      (positivePeak (y - z) + positivePeak (z - y))| ≤ 2 * ‖x - y‖ := by
    rw [show (positivePeak (x - z) + positivePeak (z - x)) -
      (positivePeak (y - z) + positivePeak (z - y)) =
      (positivePeak (x - z) - positivePeak (y - z)) +
      (positivePeak (z - x) - positivePeak (z - y)) by ring]
    linarith only [hs, hp, hn]
  unfold seedHat nodalHat
  rw [max_comm 0, max_comm 0]
  apply (abs_max_sub_max_le_abs _ _ 0).trans
  have hscale : seedScale 4 = (1 / 81 : ℝ) := by norm_num [seedScale]
  rw [hscale]
  have he : (1 - (positivePeak (x - z) + positivePeak (z - x)) / (1 / 81)) -
      (1 - (positivePeak (y - z) + positivePeak (z - y)) / (1 / 81)) =
      -81 * ((positivePeak (x - z) + positivePeak (z - x)) -
        (positivePeak (y - z) + positivePeak (z - y))) := by ring
  change |(1 - (positivePeak (x - z) + positivePeak (z - x)) / (1 / 81)) -
      (1 - (positivePeak (y - z) + positivePeak (z - y)) / (1 / 81))| ≤ _
  rw [he, abs_mul]
  norm_num
  linarith only [hsum]

/-- The fixed nodal cutoff is globally Lipschitz. Its constant depends only on dimension. -/
theorem capacitarySeed_lipschitz :
    LipschitzWith (162 * (capacitaryNodes d).card) (capacitarySeed d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
  unfold capacitarySeed
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ capacitaryNodes d, |seedHat 4 m x - seedHat 4 m y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ capacitaryNodes d, 162 * ‖x - y‖ :=
      Finset.sum_le_sum fun m _ => capacitary_seedHat_sub_le m x y
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end CoarseDeGiorgi.Endpoint

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Metric Filter
open CoarseDeGiorgi.Whitney

variable {d : ℕ}

/-- The fixed nodal seed has compact support in the ambient unit cube. -/
theorem capacitarySeed_support :
    HasCompactSupport (capacitarySeed d) ∧ tsupport (capacitarySeed d) ⊆ originCube 1 := by
  have hsub : Function.support (capacitarySeed d) ⊆
      Metric.closedBall (remoteCenter d) (3 / 81) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra hn
    exact hx (capacitarySeed_eq_zero (le_of_not_ge hn))
  have hc : IsCompact (Metric.closedBall (remoteCenter d) (3 / 81)) := isCompact_closedBall _ _
  refine ⟨HasCompactSupport.of_support_subset_isCompact hc hsub, ?_⟩
  have hts := closure_minimal hsub isClosed_closedBall
  intro x hx
  have hb := hts hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hb
  rw [originCube_eq_ball' one_pos, Metric.mem_ball, dist_zero_right]
  have ht := norm_sub_le_norm_sub_add_norm_sub x (remoteCenter d) 0
  simp only [sub_zero] at ht
  have hcn := remoteCenter_norm_le (d := d)
  linarith only [hb, ht, hcn]

end CoarseDeGiorgi.Endpoint
