import CoarseDeGiorgi.Whitney.LiftClosure
import CoarseDeGiorgi.Whitney.LiftCell
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators
noncomputable section
variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Disjointly supported fields have exactly additive unnormalized energy. -/
lemma lift_energy_finset_disjoint {ι : Type*} (ha : IsWeightedCoeffOn V a)
    (U : ι → Set (Vec d)) (G : ι → Vec d → Vec d)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hM : ∀ k, AEStronglyMeasurable (G k) (volume.restrict V))
    (hsupp : ∀ k x, x ∉ U k → G k x = 0) (S : Finset ι) :
    weightedEnergy a V (∑ k ∈ S, G k) = ∑ k ∈ S, weightedEnergy a V (G k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, weightedEnergy, Pi.zero_apply, vecDot_zero_left,
      ENNReal.ofReal_zero, lintegral_zero]
  | @insert k S hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have hzero (x : Vec d) : G k x = 0 ∨ (∑ j ∈ S, G j) x = 0 := by
      by_cases hx : x ∈ U k
      · right
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro j hj
        exact hsupp j x (fun hy => (Set.disjoint_left.mp (hdisj (Ne.symm (ne_of_mem_of_not_mem hj hk)))) hx hy)
      · exact Or.inl (hsupp k x hx)
    have he (x : Vec d) : ENNReal.ofReal (vecDot ((G k + ∑ j ∈ S, G j) x)
          (matVecMul (a x) ((G k + ∑ j ∈ S, G j) x))) =
        ENNReal.ofReal (vecDot (G k x) (matVecMul (a x) (G k x))) +
          ENNReal.ofReal (vecDot ((∑ j ∈ S, G j) x) (matVecMul (a x) ((∑ j ∈ S, G j) x))) := by
      rcases hzero x with hx | hx <;>
        simp only [Pi.add_apply, hx, zero_add, add_zero, vecDot_zero_left, ENNReal.ofReal_zero]
    change (∫⁻ x in V, _) = _
    simp_rw [he]
    rw [lintegral_add_left' (Weighted.quadratic_aestronglyMeasurable ha (hM k)).aemeasurable.ennreal_ofReal,
      ← ih]
    rfl

/-- Finite sums of zero-boundary pairs (`MemH1a0`) are zero-boundary pairs. -/
lemma lift_boundary_finset_sum [NeZero d] {ι : Type*}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    (u : ι → Vec d → ℝ) (G : ι → Vec d → Vec d)
    (hu : ∀ k, MemH1a0 a V (u k) (G k)) (S : Finset ι) :
    MemH1a0 a V (∑ k ∈ S, u k) (∑ k ∈ S, G k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz := Weighted.memH1a0_of_supported hV.isOpen ha
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => (0 : ℝ)))
      (HasCompactSupport.zero) (by change tsupport (0 : Vec d → ℝ) ⊆ V; rw [tsupport_zero]; exact empty_subset V)
    change MemH1a0 a V (fun _ => 0) (smoothGrad (fun _ => 0)) at hz
    have hgrad : smoothGrad (fun _ : Vec d => (0 : ℝ)) = fun _ => (0 : Vec d) := by
      funext x i
      simp [smoothGrad]
    rw [hgrad] at hz
    exact hz
  | @insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    exact Weighted.MemH1a0.add hV hne ha (hu k) ih

end
end CoarseDeGiorgi.Whitney
