import CoarseDeGiorgi.Weighted.Truncation.Algebra
import CoarseDeGiorgi.Weighted.PairOperations
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.IsWeightedSupersolution

namespace CoarseDeGiorgi.Harnack.Calculus

open Homogenization MeasureTheory Filter

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The negative of a weighted solution is a weighted solution. -/
theorem IsWeightedSolution.negPair (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ}
    {G : Vec d → Vec d} (hu : IsWeightedSolution a V u G) :
    IsWeightedSolution a V (-u) (-G) := by
  refine ⟨CoarseDeGiorgi.Weighted.MemH1a.neg hV hne ha hu.1, ?_⟩
  intro φ hφ hc hs
  have hp := hu.2 φ hφ hc hs
  have hpair : (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (-G x))) =
      fun x => -vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) := by
    funext x
    simp [vecDot, matVecMul]
  refine ⟨?_, ?_⟩
  · apply hp.1.neg.congr_fun_ae
    filter_upwards with x
    exact (congrFun hpair x).symm
  · calc
      ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (-G x)) =
          ∫ x in V, -vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => congrFun hpair x)
      _ = -(∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (G x))) := by
        rw [integral_neg]
      _ = 0 := by rw [hp.2]; simp

/-- A weighted solution is a weighted supersolution. -/
theorem IsWeightedSolution.isSupersolution (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ}
    {G : Vec d → Vec d} (hu : IsWeightedSolution a V u G) :
    IsWeightedSupersolution a V u G := by
  have hneg := IsWeightedSolution.negPair hV hne ha hu
  refine ⟨hneg.1, ?_⟩
  intro φ hφ hc hs hnonneg
  have hp := hneg.2 φ hφ hc hs
  exact ⟨hp.1, hp.2.le⟩

/-- Adding a constant to a weighted solution gives a weighted solution. -/
theorem IsWeightedSolution.addConst (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ}
    {G : Vec d → Vec d} (hu : IsWeightedSolution a V u G) (c : ℝ) :
    IsWeightedSolution a V (fun x => u x + c) G := by
  refine ⟨CoarseDeGiorgi.Weighted.MemH1a.add_const hV hne ha hu.1 c, ?_⟩
  intro φ hφ hc hs
  exact hu.2 φ hφ hc hs

/-- A nonnegative solution shifted by `ε > 0` is a nonnegative solution and supersolution. -/
theorem shiftedSolution_isNonnegativeSupersolution
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSolution a V u G)
    (hu_nonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    (∀ᵐ x ∂volume.restrict V, 0 ≤ u x + ε) ∧
      IsWeightedSolution a V (fun x => u x + ε) G ∧
      IsWeightedSupersolution a V (fun x => u x + ε) G := by
  refine ⟨hu_nonneg.mono (fun x hx => by linarith), ?_, ?_⟩
  · exact IsWeightedSolution.addConst hV hne ha hu ε
  · exact IsWeightedSolution.isSupersolution hV hne ha
      (IsWeightedSolution.addConst hV hne ha hu ε)

end CoarseDeGiorgi.Harnack.Calculus
