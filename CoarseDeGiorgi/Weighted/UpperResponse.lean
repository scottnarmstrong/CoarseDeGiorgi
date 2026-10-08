module

public import CoarseDeGiorgi.Weighted.UpperResponsePositive

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

/-- The zero pair is an admissible competitor in every dimension. -/
theorem upper_zero_solution {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    CoarseDeGiorgi.IsWeightedSolution a V (fun _ => 0) (fun _ => 0) := by
  have hc : IsSmoothCore a V (fun _ => 0) := by
    refine ⟨contDiffOn_const, integrableOn_zero, ?_⟩
    simp [CoarseDeGiorgi.weightedEnergy, CoarseDeGiorgi.smoothGrad, vecDot, matVecMul]
  have hm : MemH1a a V (fun _ => 0) (fun _ => 0) := by
    have hg : smoothGrad (fun _ : Vec d => (0 : ℝ)) = fun _ => (0 : Vec d) := by
      funext x i
      simp [smoothGrad, CoarseDeGiorgi.smoothGrad]
    rw [← hg]
    exact memH1a_of_isSmoothCore hV ha hc
  apply isWeightedSolution_of_orthogonality hV ha hm
  intro w H _
  simp [vecDot, matVecMul]

/-- In dimension zero the literal directional supremum equals zero. -/
theorem upper_response_dimension_zero {V : Set (Vec 0)} {a : CoeffField 0}
    (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) (e : Vec 0) :
    CoarseDeGiorgi.upperDirectionalResponseSol a V e = 0 := by
  unfold CoarseDeGiorgi.upperDirectionalResponseSol
  apply le_antisymm
  · refine iSup_le fun w => iSup_le fun G => iSup_le fun _ => ?_
    simp [vecDot, volumeAverage]
  · have hz := upper_zero_solution hV ha
    have hb : ((volumeAverage V (fun _ : Vec 0 => (0 : ℝ)) : ℝ) : EReal) ≤
        ⨆ (w : Vec 0 → ℝ) (G : Vec 0 → Vec 0)
          (_ : CoarseDeGiorgi.IsWeightedSolution a V w G),
          ((volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
            2 * vecDot e (matVecMul (a x) (G x))) : ℝ) : EReal) :=
      le_iSup_of_le (fun _ : Vec 0 => (0 : ℝ))
      (le_iSup_of_le (fun _ : Vec 0 => (0 : Vec 0)) (le_iSup_of_le hz (by simp [vecDot, volumeAverage])))
    simpa [vecDot, volumeAverage] using hb

/-- Existence and uniqueness of the upper-response matrix, in every dimension. -/
theorem upperResponse_existsUnique_proved {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    ∃! A : Mat d, A.PosDef ∧ ∀ e : Vec d,
      ((vecDot e (matVecMul A e) : ℝ) : EReal) =
        CoarseDeGiorgi.upperDirectionalResponseSol a V e := by
  by_cases hd : d = 0
  · subst d
    refine ⟨0, ⟨?_, ?_⟩, fun M _ => Subsingleton.elim M 0⟩
    · apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · exact Matrix.isHermitian_zero
      · intro e he
        exact False.elim (he (Subsingleton.elim e 0))
    · intro e
      rw [upper_response_dimension_zero hV.isOpen ha e]
      simp [vecDot]
  · have : NeZero d := ⟨hd⟩
    exact upperResponse_existsUnique_of_neZero hV hV₀ ha

end CoarseDeGiorgi.Weighted
