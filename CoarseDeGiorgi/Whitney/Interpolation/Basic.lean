import CoarseDeGiorgi.Whitney.SeedInterpolation

/-! # Kuhn hats at every integer scale

For `n : ℤ` the mesh `3^n` Kuhn hats are the level-zero hats composed with the dilation
`x ↦ 3^(-n) x`.  Everything about them (interpolation at nodes, refinement, support) is
transported from the level-zero development of the Whitney seed. -/

namespace CoarseDeGiorgi.Whitney.Interpolation

open Homogenization

noncomputable section

variable {d : ℕ}

/-- Dilation sending mesh `3^n` to mesh `1`. -/
def dil (n : ℤ) (x : Vec d) : Vec d := (3 : ℝ) ^ (-n) • x

/-- The node of mesh `3^n` with lattice index `m`. -/
def nodeN (n : ℤ) (m : Fin d → ℤ) : Vec d := fun i => (3 : ℝ) ^ n * ((m i : ℝ) + 1 / 2)

/-- The Kuhn hat of mesh `3^n` at the node of index `m`. -/
def hatN (n : ℤ) (m : Fin d → ℤ) (x : Vec d) : ℝ := seedHat 0 m (dil n x)

/-- Piecewise affine interpolation of the values of `f` at the nodes of mesh `3^n`. -/
def interpP (n : ℤ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑' m : Fin d → ℤ, f (nodeN n m) * hatN n m x

theorem seedScale_zero : seedScale 0 = 1 := by simp [seedScale]

theorem seedNode_zero (m : Fin d → ℤ) : seedNode 0 m = fun i => (m i : ℝ) + 1 / 2 := by
  funext i; simp [seedNode, seedScale_zero]

theorem dil_nodeN (n : ℤ) (m : Fin d → ℤ) : dil n (nodeN n m) = seedNode 0 m := by
  funext i
  simp only [dil, nodeN, Pi.smul_apply, smul_eq_mul, seedNode_zero]
  rw [← mul_assoc, ← zpow_add₀ (by norm_num)]
  simp

theorem positivePeak_smul {c : ℝ} (hc : 0 ≤ c) (x : Vec d) :
    positivePeak (c • x) = c * positivePeak x := by
  unfold positivePeak
  have : (fun i => max ((c • x) i) 0) = c • (fun i => max (x i) 0) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  rw [this, norm_smul, Real.norm_of_nonneg hc]

theorem hatN_apply_node (n : ℤ) (m m' : Fin d → ℤ) :
    hatN n m (nodeN n m') = if m = m' then 1 else 0 := by
  rw [hatN, dil_nodeN, ← seedHat_at_node 0 m m']

theorem pos_zpow3 (n : ℤ) : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _

theorem abs_sub_lt_of_hatN_ne_zero {n : ℤ} {m : Fin d → ℤ} {x : Vec d}
    (h : hatN n m x ≠ 0) (i : Fin d) : |x i - nodeN n m i| < (3 : ℝ) ^ n := by
  have h1 := norm_sub_lt_of_nodalHat_ne_zero (s := seedScale 0) (seedScale_pos 0) h
  rw [seedScale_zero] at h1
  have h2 : dil n x - seedNode 0 m = (3 : ℝ) ^ (-n) • (x - nodeN n m) := by
    rw [← dil_nodeN n m, dil, dil, smul_sub]
  rw [h2, norm_smul, Real.norm_of_nonneg (pos_zpow3 _).le] at h1
  have h3 : |x i - nodeN n m i| ≤ ‖x - nodeN n m‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x - nodeN n m) i
  have h4 : (3 : ℝ) ^ (-n) * ‖x - nodeN n m‖ < 1 := h1
  have h5 : (3 : ℝ) ^ n * (3 : ℝ) ^ (-n) = 1 := by
    rw [← zpow_add₀ (by norm_num)]; simp
  have h6 : ‖x - nodeN n m‖ < (3 : ℝ) ^ n := by
    have := mul_lt_mul_of_pos_left h4 (pos_zpow3 n)
    nlinarith [this, h5, norm_nonneg (x - nodeN n m), pos_zpow3 n]
  exact h3.trans_lt h6

theorem interpP_node (n : ℤ) (f : Vec d → ℝ) (m : Fin d → ℤ) :
    interpP n f (nodeN n m) = f (nodeN n m) := by
  classical
  unfold interpP
  rw [tsum_eq_single m]
  · rw [hatN_apply_node, ite_eq_left rfl, mul_one]
  · intro m' hm'
    rw [hatN_apply_node, ite_eq_right hm', mul_zero]

theorem interpP_eq_seedInterpolation (n : ℤ) (f : Vec d → ℝ) (x : Vec d) :
    interpP n f x = seedInterpolation 0 (fun m => f (nodeN n m)) (dil n x) := rfl

theorem seedHat_one (m : Fin d → ℤ) (y : Vec d) :
    seedHat 1 m y = seedHat 0 m ((3 : ℝ) • y) := by
  have hs : seedScale 1 = 1 / 3 := by simp [seedScale]
  have hn : seedNode 1 m = (1 / 3 : ℝ) • seedNode 0 m := by
    funext i; simp [seedNode, hs, seedScale_zero]
  have h1 : y - seedNode 1 m = (1 / 3 : ℝ) • ((3 : ℝ) • y - seedNode 0 m) := by
    rw [hn, smul_sub, smul_smul]; norm_num
  have h2 : seedNode 1 m - y = (1 / 3 : ℝ) • (seedNode 0 m - (3 : ℝ) • y) := by
    rw [hn, smul_sub, smul_smul]; norm_num
  unfold seedHat nodalHat
  rw [hs, seedScale_zero, h1, h2, positivePeak_smul (by norm_num), positivePeak_smul (by norm_num)]
  congr 1
  field_simp

theorem interpP_refine (n : ℤ) (f : Vec d → ℝ) (x : Vec d) :
    interpP n f x = interpP (n - 1) (interpP n f) x := by
  have h := seedInterpolation_refinement (d := d) 0 (fun m => f (nodeN n m)) (dil n x)
  rw [interpP_eq_seedInterpolation, h]
  show ∑' m : Fin d → ℤ, seedInterpolation 0 (fun m => f (nodeN n m)) (seedNode (0 + 1) m) *
      seedHat (0 + 1) m (dil n x) = ∑' m : Fin d → ℤ, interpP n f (nodeN (n - 1) m) *
      hatN (n - 1) m x
  apply tsum_congr
  intro m
  congr 1
  · rw [interpP_eq_seedInterpolation]
    congr 2
    funext i
    simp only [dil, nodeN, Pi.smul_apply, smul_eq_mul, seedNode, seedScale]
    rw [← mul_assoc, ← zpow_add₀ (by norm_num)]
    have : -n + (n - 1) = -((0 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
  · rw [hatN, seedHat_one]
    congr 1
    funext i
    simp only [dil, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← zpow_one_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 2
    ring

theorem continuous_seedInterpolation_zero (c : (Fin d → ℤ) → ℝ) :
    Continuous (seedInterpolation 0 c : Vec d → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro y0
  have hS := finite_seedNodes_in_ball (d := d) 0 (‖y0‖ + 2)
  have hev : (fun y => ∑ m ∈ hS.toFinset, c m * seedHat 0 m y) =ᶠ[nhds y0]
      seedInterpolation 0 c := by
    filter_upwards [Metric.ball_mem_nhds y0 one_pos] with y hy
    unfold seedInterpolation
    symm
    apply tsum_eq_sum
    intro m hm
    by_contra hne
    apply hm
    have hh : seedHat 0 m y ≠ 0 := right_ne_zero_of_mul hne
    have h1 := norm_sub_lt_of_nodalHat_ne_zero (seedScale_pos 0) hh
    rw [seedScale_zero] at h1
    have h2 : ‖y - y0‖ < 1 := by simpa [dist_eq_norm] using hy
    rw [Set.Finite.mem_toFinset]
    show ‖seedNode 0 m‖ ≤ ‖y0‖ + 2
    have h3 := norm_sub_norm_le (seedNode 0 m) y
    have h4 := norm_sub_norm_le y y0
    rw [norm_sub_rev] at h3
    linarith
  refine ContinuousAt.congr ?_ hev
  apply Continuous.continuousAt
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul (by
    unfold seedHat
    exact continuous_nodalHat _ _)

theorem continuous_interpP (n : ℤ) (f : Vec d → ℝ) : Continuous (interpP n f) := by
  have : interpP n f = seedInterpolation 0 (fun m => f (nodeN n m)) ∘ dil n := by
    funext x; rfl
  rw [this]
  exact (continuous_seedInterpolation_zero _).comp (by unfold dil; fun_prop)

end

end CoarseDeGiorgi.Whitney.Interpolation
