module

public import CoarseDeGiorgi.Statements.OriginCube
public import Homogenization.Geometry.ConvexDomain
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Elementary geometry of the cubes `originCube r`. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Metric

variable {d : ℕ}

theorem originCube_eq_ball' {r : ℝ} (hr : 0 < r) :
    originCube (d := d) r = Metric.ball (0 : Vec d) (r / 2) := by
  ext x
  simp only [originCube, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff (by linarith : 0 < r / 2), Real.norm_eq_abs, abs_lt]

theorem originCube_domain {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (originCube (d := d) r) := by
  rw [originCube_eq_ball' hr]
  exact isOpenBoundedConvexDomain_ball 0 (by linarith)

theorem originCube_nonempty {r : ℝ} (hr : 0 < r) : (originCube (d := d) r).Nonempty := by
  rw [originCube_eq_ball' hr]
  exact ⟨0, mem_ball_self (by linarith)⟩

theorem originCube_mono' {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (h : r ≤ R) :
    originCube (d := d) r ⊆ originCube R := by
  rw [originCube_eq_ball' hr, originCube_eq_ball' hR]
  exact ball_subset_ball (by linarith)

theorem closure_originCube_subset {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (h : r < R) :
    closure (originCube (d := d) r) ⊆ originCube R := by
  rw [originCube_eq_ball' hr, originCube_eq_ball' hR, closure_ball _ (by linarith)]
  exact closedBall_subset_ball (by linarith)

theorem isCompact_closure_originCube {r : ℝ} (hr : 0 < r) :
    IsCompact (closure (originCube (d := d) r)) := by
  rw [originCube_eq_ball' hr, closure_ball _ (by linarith)]
  exact isCompact_closedBall _ _

end CoarseDeGiorgi.Endpoint
