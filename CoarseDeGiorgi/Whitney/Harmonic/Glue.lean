import CoarseDeGiorgi.Whitney.Harmonic.Geometry
import CoarseDeGiorgi.Statements.EuclidLipConst
import CoarseDeGiorgi.Foundations.Euclid.Basic
import CoarseDeGiorgi.Foundations.FracGeometry.Defs
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Normed.Affine.Convex

/-! Gluing of Lipschitz functions across the reference cube; Euclidean Lipschitz constants. -/

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

variable {d : ℕ}

/-- A segment from a point of a closed set to a point outside meets the frontier. -/
theorem segment_meets_frontier {B : Set (Vec d)} (hB : IsClosed B) {x y : Vec d}
    (hx : x ∈ B) (hy : y ∉ B) : ∃ p ∈ segment ℝ x y, p ∈ frontier B := by
  by_contra hno
  push Not at hno
  have hconn : IsPreconnected (segment ℝ x y) := (convex_segment x y).isPreconnected
  have hsub : segment ℝ x y ⊆ interior B ∪ (closure B)ᶜ := by
    intro p hp
    by_cases hpB : p ∈ closure B
    · left
      by_contra hpi
      exact hno p hp ⟨hpB, hpi⟩
    · right; exact hpB
  have hxi : x ∈ interior B := by
    by_contra hxi
    exact hno x (left_mem_segment ℝ x y) ⟨subset_closure hx, hxi⟩ |>.elim
  obtain ⟨p, _, hp1, hp2⟩ := hconn (interior B) (closure B)ᶜ isOpen_interior isClosed_closure.isOpen_compl
    hsub ⟨x, left_mem_segment ℝ x y, hxi⟩
    ⟨y, right_mem_segment ℝ x y, by rwa [hB.closure_eq]⟩
  exact hp2 (interior_subset.trans subset_closure hp1)

open scoped Classical in
/-- Gluing a function Lipschitz on the closed cube `B` to one Lipschitz off the open cube. -/
theorem lipschitz_glue {τ : ℝ} (hτ : 0 < τ) {K₁ K₂ : ℝ≥0} {F w : Vec d → ℝ}
    (hF : LipschitzOnWith K₁ F (CoarseDeGiorgi.originCube (d := d) τ)ᶜ)
    (hw : LipschitzOnWith K₂ w (CoarseDeGiorgi.closedReferenceCube (d := d) τ))
    (hagree : ∀ y ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ,
      y ∉ CoarseDeGiorgi.originCube (d := d) τ → w y = F y) :
    LipschitzWith (max K₁ K₂)
      (fun x => if x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ then w x else F x) := by
  classical
  set B := CoarseDeGiorgi.closedReferenceCube (d := d) τ with hB
  have hBc : IsClosed B := isClosed_closedRef hτ.le
  have hBconv : Convex ℝ B := by
    rw [hB, closedRef_eq_closedBall hτ.le]; exact convex_closedBall _ _
  have hOB : CoarseDeGiorgi.originCube (d := d) τ ⊆ B := by
    intro x hx i
    have := hx i
    exact abs_le.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  have hmax1 : (K₁ : ℝ) ≤ max K₁ K₂ := by exact_mod_cast le_max_left _ _
  have hmax2 : (K₂ : ℝ) ≤ max K₁ K₂ := by exact_mod_cast le_max_right _ _
  -- mixed case
  have mixed : ∀ x y, x ∈ B → y ∉ B →
      |w x - F y| ≤ (max K₁ K₂ : ℝ≥0) * dist x y := by
    intro x y hx hy
    obtain ⟨p, hps, hpf⟩ := segment_meets_frontier hBc hx hy
    have hpB : p ∈ B := hBc.frontier_subset hpf
    have hpO : p ∉ CoarseDeGiorgi.originCube (d := d) τ := by
      intro hp
      have : p ∈ interior B := interior_maximal hOB
        (by rw [Whitney.source_originCube_eq_ball hτ]; exact Metric.isOpen_ball) hp
      exact hpf.2 this
    have hsum : dist x p + dist p y = dist x y := dist_add_dist_of_mem_segment hps
    have h1 := hw.dist_le_mul x hx p hpB
    have hyO : y ∈ (CoarseDeGiorgi.originCube (d := d) τ)ᶜ := fun h => hy (hOB h)
    have h2 := hF.dist_le_mul p (hpO) y hyO
    rw [Real.dist_eq] at h1 h2
    have hwp := hagree p hpB hpO
    calc |w x - F y| = |(w x - w p) + (F p - F y)| := by rw [hwp]; ring_nf
      _ ≤ |w x - w p| + |F p - F y| := abs_add_le _ _
      _ ≤ K₂ * dist x p + K₁ * dist p y := add_le_add h1 h2
      _ ≤ (max K₁ K₂ : ℝ≥0) * dist x p + (max K₁ K₂ : ℝ≥0) * dist p y := by
          gcongr
      _ = _ := by rw [← mul_add, hsum]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
  · simp only [hx, hy, ite_true]
    have := hw.dist_le_mul x hx y hy
    rw [Real.dist_eq] at this
    exact this.trans (by gcongr)
  · simp only [hx, hy, ite_true, ite_false]
    exact mixed x y hx hy
  · simp only [hx, hy, ite_true, ite_false]
    rw [abs_sub_comm, dist_comm]
    exact mixed y x hy hx
  · simp only [hx, hy, ite_false]
    have := hF.dist_le_mul x (fun h => hx (hOB h)) y (fun h => hy (hOB h))
    rw [Real.dist_eq] at this
    exact this.trans (by gcongr)

/-- A finite Euclidean Lipschitz constant gives Lipschitz continuity in the ambient metric. -/
theorem lipschitzOn_of_euclidLipConst_lt_top {S : Set (Vec d)} {F : Vec d → ℝ}
    (h : CoarseDeGiorgi.euclidLipConst S F < ⊤) : ∃ K : ℝ≥0, LipschitzOnWith K F S := by
  unfold CoarseDeGiorgi.euclidLipConst at h
  obtain ⟨K, hK⟩ := iInf_lt_iff.mp h
  obtain ⟨hcond, hlt⟩ := iInf_lt_iff.mp hK
  refine ⟨K * (Real.sqrt d).toNNReal, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h1 := hcond x hx y hy
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg K.coe_nonneg
    (Foundations.Euclid.eDist2_nonneg x y))).mp h1
  rw [Real.dist_eq]
  have h3 : CoarseDeGiorgi.euclidDist x y ≤ Real.sqrt d * dist x y :=
    Foundations.Euclid.eDist2_le_sqrt_mul_dist x y
  calc |F x - F y| ≤ K * CoarseDeGiorgi.euclidDist x y := h2
    _ ≤ K * (Real.sqrt d * dist x y) := by gcongr
    _ = _ := by simp only [NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]; ring

end CoarseDeGiorgi.Whitney.Harmonic
