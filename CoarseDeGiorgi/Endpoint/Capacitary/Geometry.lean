module

public import CoarseDeGiorgi.Endpoint.Interface
public import CoarseDeGiorgi.Endpoint.Source.Geometry
public import CoarseDeGiorgi.Endpoint.Source.Functional
public import CoarseDeGiorgi.Endpoint.Capacitary.Test

/-! The remote obstacle cube and its capacitary function. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Metric Filter
open CoarseDeGiorgi.Weighted

variable {d : ℕ}

/-- The remote cube is a ball for the ambient maximum norm. -/
theorem remoteCube_eq_ball {ρ : ℝ} (hρ : 0 < ρ) :
    remoteCube d ρ = Metric.ball (remoteCenter d) (ρ / 54) := by
  unfold remoteCube
  rw [originCube_eq_ball' (mul_pos hρ (zpow_pos (by norm_num) _))]
  have hs : (ρ * (3 : ℝ) ^ (-3 : ℤ)) / 2 = ρ / 54 := by norm_num; ring
  ext x
  simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, sub_zero, hs]

/-- The remote cube is an open bounded convex domain. -/
theorem remoteCube_domain {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpenBoundedConvexDomain (remoteCube d ρ) := by
  rw [remoteCube_eq_ball hρ]
  exact isOpenBoundedConvexDomain_ball _ (div_pos hρ (by norm_num))

/-- The remote center has maximum norm at most `34/81`, in every dimension. -/
theorem remoteCenter_norm_le : ‖remoteCenter d‖ ≤ (34 / 81 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 34 / 81)).mpr
  intro i
  simp only [remoteCenter, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- The closure of the remote cube lies inside `(15/16)□₀`. -/
theorem closure_remoteCube_subset_interior :
    closure (remoteCube d 1) ⊆ originCube (15 / 16) := by
  rw [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1), closure_ball _ (by norm_num),
    originCube_eq_ball' (by norm_num : (0 : ℝ) < 15 / 16)]
  intro x hx
  have h := norm_sub_le_norm_sub_add_norm_sub x (remoteCenter d) 0
  simp only [Metric.mem_closedBall, dist_eq_norm] at hx
  simp only [Metric.mem_ball, dist_zero_right]
  have hc := remoteCenter_norm_le (d := d)
  simp only [sub_zero] at h
  linarith only [h, hx, hc]

/-- The remote cube is exterior to the closed `(3/4)□₀`. -/
theorem remoteCube_subset_exterior [NeZero d] :
    remoteCube d 1 ⊆ originCube 1 \ closure (originCube (3 / 4)) := by
  intro x hx
  have hi := closure_remoteCube_subset_interior (subset_closure hx)
  refine ⟨originCube_mono' (by norm_num) one_pos (by norm_num) hi, ?_⟩
  rw [originCube_eq_ball' (by norm_num : (0 : ℝ) < 3 / 4), closure_ball _ (by norm_num)]
  intro hc
  have hc' : ‖x‖ ≤ (3 / 4 : ℝ) / 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hc
  have hx' : ‖x - remoteCenter d‖ < (1 : ℝ) / 54 := by
    simpa only [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1), Metric.mem_ball,
      dist_eq_norm] using hx
  have hcoord : |x (0 : Fin d) - 34 / 81| < (1 : ℝ) / 54 := by
    have := (norm_le_pi_norm (x - remoteCenter d) (0 : Fin d)).trans_lt hx'
    simpa only [Pi.sub_apply, remoteCenter, Fin.val_zero, ite_true, Real.norm_eq_abs] using this
  have hcoord' : |x (0 : Fin d)| ≤ (3 / 4 : ℝ) / 2 :=
    (show ‖x (0 : Fin d)‖ ≤ ‖x‖ from norm_le_pi_norm x (0 : Fin d)).trans hc'
  have hlo := (abs_lt.mp hcoord).1
  have hhi := le_abs_self (x (0 : Fin d))
  linarith only [hlo, hcoord', hhi]

/-- A compactly supported smooth function is admissible for the remote obstacle. -/
theorem remote_obstacle_nonempty [NeZero d]
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    ∃ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a (originCube 1) u G ∧
      (∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → 1 ≤ u x) := by
  have hhalf : closure (remoteCube d (1 / 2)) ⊆ closure (remoteCube d 1) := by
    apply closure_mono
    rw [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1 / 2),
      remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1)]
    exact ball_subset_ball (by norm_num)
  have hsub : closure (remoteCube d (1 / 2)) ⊆ originCube 1 := fun x hx =>
    originCube_mono' (by norm_num : (0 : ℝ) < 15 / 16) one_pos (by norm_num)
      (closure_remoteCube_subset_interior (hhalf hx))
  have hK : IsCompact (closure (remoteCube d (1 / 2))) := by
    rw [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1 / 2), closure_ball _ (by norm_num)]
    exact isCompact_closedBall _ _
  obtain ⟨φ, hφ, hc, hs, _, hφ1⟩ := exists_cutoff01 (originCube_domain one_pos).isOpen hK hsub
  refine ⟨φ, smoothGrad φ, memH1a0_of_supported (originCube_domain one_pos).isOpen ha hφ hc hs, ?_⟩
  exact Eventually.of_forall fun x hx => (hφ1 x (subset_closure hx)).ge

/-- Step 4: the remote obstacle has a bounded capacitary supersolution of least energy. -/
theorem remote_capacitary_exists [NeZero d]
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    ∃ (ψ : Vec d → ℝ) (Gψ : Vec d → Vec d), MemH1a0 a (originCube 1) ψ Gψ ∧
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → ψ x = 1) ∧
      IsWeightedSupersolution a (originCube 1) ψ Gψ ∧
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a (originCube 1) u G →
        (∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → 1 ≤ u x) →
        weightedEnergy a (originCube 1) Gψ ≤ weightedEnergy a (originCube 1) G := by
  have hV := originCube_domain (d := d) one_pos
  have hne := originCube_nonempty (d := d) one_pos
  obtain ⟨ψ, Gψ, hψ, hψ01, hψQ, hmin⟩ := exists_bounded_capacitary_minimizer hV hne ha
    (remoteCube d (1 / 2)) (remote_obstacle_nonempty a ha)
  exact ⟨ψ, Gψ, hψ, hψ01, hψQ,
    capacitary_isWeightedSupersolution hV hne ha hψ
      (hψQ.mono fun x hx hxQ => (hx hxQ).ge) hmin, hmin⟩

end CoarseDeGiorgi.Endpoint
