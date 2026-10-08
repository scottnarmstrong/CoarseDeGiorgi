import CoarseDeGiorgi.Weighted.UpperSpecNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Sums of positive semidefinite matrices controlled by their quadratic forms -/

namespace CoarseDeGiorgi.Cubical

open Homogenization
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The quadratic form of a matrix. -/
noncomputable abbrev qf (M : Mat d) (e : Vec d) : ℝ := vecDot e (matVecMul M e)

lemma qf_apply (M : Mat d) (e : Vec d) : qf M e = ∑ i, ∑ j, e i * M i j * e j := by
  simp only [qf, vecDot, matVecMul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma qf_add (M N : Mat d) (e : Vec d) : qf (M + N) e = qf M e + qf N e := by
  simp only [qf_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma qf_smul (c : ℝ) (M : Mat d) (e : Vec d) : qf (c • M) e = c * qf M e := by
  simp only [qf_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma qf_sub (M N : Mat d) (e : Vec d) : qf (M - N) e = qf M e - qf N e := by
  simp only [qf_apply, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma qf_single (M : Mat d) (j : Fin d) : qf M (Pi.single j 1) = M j j := by
  simp [qf_apply, Pi.single_apply]

lemma qf_single_add (M : Mat d) (j k : Fin d) :
    qf M (Pi.single j 1 + Pi.single k 1) = M j j + M j k + M k j + M k k := by
  have : ∀ i, ((Pi.single j 1 + Pi.single k 1 : Vec d) i) =
      (if i = j then 1 else 0) + (if i = k then 1 else 0) := by
    intro i; simp [Pi.single_apply]
  simp only [qf_apply, this]
  simp [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite]
  ring

lemma entry_eq (M : Mat d) (hM : M.IsHermitian) (j k : Fin d) :
    M j k = (qf M (Pi.single j 1 + Pi.single k 1) - qf M (Pi.single j 1) - qf M (Pi.single k 1)) / 2 := by
  rw [qf_single_add M j k, qf_single, qf_single]
  have hs : M k j = M j k := by
    have := congrFun (congrFun hM.eq j) k
    simpa [Matrix.conjTranspose_apply] using this
  rw [hs]; ring

/-- Entries of Hermitian matrices are controlled by quadratic forms. -/
lemma summable_of_qf {ι : Type*} (N : ι → Mat d) (hN : ∀ i, (N i).IsHermitian)
    (hq : ∀ e, Summable (fun i => qf (N i) e)) : Summable N := by
  let E : (Fin d → Fin d → ℝ) ≃L[ℝ] Mat d :=
    (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  rw [← E.symm.summable]
  rw [Pi.summable]; intro j; rw [Pi.summable]; intro k
  have h1 := (hq (Pi.single j 1 + Pi.single k 1)).sub (hq (Pi.single j 1)) |>.sub (hq (Pi.single k 1))
  have h2 := h1.div_const 2
  refine h2.congr ?_
  intro i
  simpa [E] using (entry_eq (N i) (hN i) j k).symm

lemma qf_nonneg {M : Mat d} (hM : M.PosSemidef) (e : Vec d) : 0 ≤ qf M e := by
  have h := hM.dotProduct_mulVec_nonneg e
  simpa only [qf, vecDot, matVecMul, Matrix.mulVec, dotProduct, star_trivial] using h

/-- Entrywise continuous linear equivalence. -/
noncomputable def entryEquiv : (Fin d → Fin d → ℝ) ≃L[ℝ] Mat d :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

lemma hasSum_entry {ι : Type*} {N : ι → Mat d} {S : Mat d} (h : HasSum N S) (j k : Fin d) :
    HasSum (fun i => N i j k) (S j k) := by
  have h1 := (entryEquiv (d := d)).symm.hasSum.mpr h
  exact Pi.hasSum.mp (Pi.hasSum.mp h1 j) k

/-- The quadratic form as a continuous linear functional of the matrix. -/
noncomputable def qfCLM (e : Vec d) : Mat d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => qf M e
      map_add' := fun M N => qf_add M N e
      map_smul' := fun c M => by simpa using qf_smul c M e }

lemma qf_tsum {ι : Type*} {N : ι → Mat d} (h : Summable N) (e : Vec d) :
    qf (∑' i, N i) e = ∑' i, qf (N i) e :=
  ((qfCLM e).hasSum h.hasSum).tsum_eq.symm

lemma psdSum {ι : Type*} (N : ι → Mat d) (hN : ∀ i, (N i).PosSemidef)
    (hq : ∀ e, Summable (fun i => qf (N i) e)) (M : Mat d) (hM : M.PosSemidef)
    (hle : ∀ e, qf M e ≤ ∑' i, qf (N i) e) :
    Summable (fun i => ‖N i‖) ∧ (∑' i, N i - M).PosSemidef := by
  have hs : Summable N := summable_of_qf N (fun i => (hN i).isHermitian) hq
  refine ⟨summable_norm_iff.mpr hs, ?_⟩
  have hherm : (∑' i, N i).IsHermitian := by
    ext j k
    have h1 := (hasSum_entry hs.hasSum j k).tsum_eq
    have h2 := (hasSum_entry hs.hasSum k j).tsum_eq
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [← h1, ← h2]
    congr 1; ext i
    have := congrFun (congrFun (hN i).isHermitian.eq k) j
    simpa [Matrix.conjTranspose_apply] using this.symm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hherm.sub hM.isHermitian) ?_
  intro x
  have := (qf_sub (∑' i, N i) M x) ▸ (sub_nonneg.mpr ((hle x).trans_eq (qf_tsum hs x).symm))
  simpa [qf, vecDot, matVecMul, Matrix.mulVec, dotProduct] using this

/-- The abstract matrix conclusion in dimension zero. -/
lemma psd_zero_dim {ι : Type} (N : ι → Mat 0) (M : Mat 0) :
    Summable (fun i => ‖N i‖) ∧ (∑' i, N i - M).PosSemidef := by
  have h0 : ∀ A : Mat 0, A = 0 := fun A => Subsingleton.elim _ _
  refine ⟨?_, ?_⟩
  · simp only [h0 (N _), norm_zero]; exact summable_zero
  · rw [h0 (∑' i, N i - M)]; exact Matrix.PosSemidef.zero

end CoarseDeGiorgi.Cubical
