import CoarseDeGiorgi.Endpoint.Reconstruction.SmoothReconstruction
import CoarseDeGiorgi.Endpoint.Reconstruction.MomentTail
import CoarseDeGiorgi.Endpoint.Morrey.Approximation

/-! # A reconstruction limit inherits its summable block tail bound -/
namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section

theorem sum_Icc_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N j : ℕ) :
    (∑ k ∈ Finset.Icc 1 (N + j), f k) =
      (∑ k ∈ Finset.Icc 1 N, f k) + ∑ k ∈ Finset.Icc (N + 1) (N + j), f k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + j + 1), ih,
      Finset.sum_Icc_succ_top (by omega : N + 1 ≤ N + j + 1), add_assoc]

theorem reconstruction_tail_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (w : ℕ → α → ℝ)
    (hw : ∀ k, AEStronglyMeasurable (w k) μ) (c : ℕ → ℝ≥0∞) (C E : ℝ≥0∞)
    (hbound : ∀ k, 1 ≤ k → eLpNorm (w k) p μ ≤ C * c k * E)
    (hconv : Tendsto (fun N => eLpNorm (fun x => f x - ∑ k ∈ Finset.Icc 1 N, w k x) p μ)
      atTop (𝓝 0)) (N : ℕ) :
    eLpNorm (fun x => f x - ∑ k ∈ Finset.Icc 1 N, w k x) p μ ≤ C * blockTail c N * E := by
  let g : ℕ → α → ℝ := fun j x => ∑ k ∈ Finset.Icc (N + 1) (N + j), w k x
  have hsum (j : ℕ) : eLpNorm (g j) p μ ≤ C * blockTail c N * E := by
    have hnorm := eLpNorm_sum_le (μ := μ) (f := w) (s := Finset.Icc (N + 1) (N + j)) hp
    have hb : (∑ k ∈ Finset.Icc (N + 1) (N + j), eLpNorm (w k) p μ) ≤
        C * (∑ k ∈ Finset.Icc (N + 1) (N + j), c k) * E := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_le_sum fun k hk => hbound k (by have := (Finset.mem_Icc.mp hk).1; omega)
    rw [show g j = ∑ k ∈ Finset.Icc (N + 1) (N + j), w k from (Finset.sum_fn _ _).symm]
    refine hnorm.trans (hb.trans ?_)
    gcongr
    exact sum_Icc_le_blockTail c N (N + j)
  have hnormconv : Tendsto (fun j => eLpNorm
      (g j - (fun x => f x - ∑ k ∈ Finset.Icc 1 N, w k x)) p μ) atTop (𝓝 0) := by
    have heq (j : ℕ) : g j - (fun x => f x - ∑ k ∈ Finset.Icc 1 N, w k x) =
        -(fun x => f x - ∑ k ∈ Finset.Icc 1 (N + j), w k x) := by
      funext x
      dsimp [g]
      rw [sum_Icc_split]
      ring
    simp_rw [heq, eLpNorm_neg]
    exact hconv.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat N)
  have hgm (j : ℕ) : AEStronglyMeasurable (g j) μ := by
    rw [show g j = ∑ k ∈ Finset.Icc (N + 1) (N + j), w k from (Finset.sum_fn _ _).symm]
    exact Finset.aestronglyMeasurable_sum _ (fun k _ => hw k)
  have hm : AEStronglyMeasurable (fun x => f x - ∑ k ∈ Finset.Icc 1 N, w k x) μ :=
    hf.sub (by
      simpa only [Finset.sum_fn] using
        Finset.aestronglyMeasurable_sum (Finset.Icc 1 N) (fun k _ => hw k))
  exact Morrey.eLpNorm_le_of_tendstoInMeasure_bound hgm hm
    (tendstoInMeasure_of_tendsto_eLpNorm (ne_of_gt (zero_lt_one.trans_le hp)) hnormconv)
    tendsto_const_nhds hsum

end
end CoarseDeGiorgi.Endpoint.Reconstruction
