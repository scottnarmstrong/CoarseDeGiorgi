import CoarseDeGiorgi.SharpnessExamples.BesovLebesgue
import CoarseDeGiorgi.SharpnessExamples.NearAxis
import CoarseDeGiorgi.SharpnessExamples.NearAxisReplacement
import CoarseDeGiorgi.SharpnessExamples.ScalarSumSubsolution
import CoarseDeGiorgi.Statements.BesovCubeNorm
import CoarseDeGiorgi.Statements.Csol

/-! # Sharpness of the coefficient range, with cube quasi-norms and unboundedness near the axis

Theorem F of the paper, assembled from the scalar cylinder construction: the finiteness of the
cube quasi-norms (summed bound over the scales), of the Lebesgue norms in the case of order zero,
and the essential unboundedness of the solution near every point of the singular segment.
-/

open Homogenization MeasureTheory Topology
open CoarseDeGiorgi.Weighted
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem sharpness_besov_proved (d : ℕ) (hd : 3 ≤ d) (ξ ζ α β : ℝ)
    (hξ : 1 < ξ) (hζ : 1 < ζ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (θ₀ : ℝ) (hθ₀def : θ₀ = 1 - (α + β) / 2 - ((d : ℝ) - 1) / 2 * (1 / ξ + 1 / ζ))
    (hθ₀ : θ₀ ≤ 0) :
    ∃ a : Vec d → ℝ,
      Measurable a ∧ (∀ x, 0 < a x) ∧
      (∀ x x' : Vec d, (∀ i : Fin d, (i : ℕ) ≠ 0 → x i = x' i) → a x = a x') ∧
      ∃ (_ha : IsWeightedCoeffOn (originCube 1) (fun x => a x • (1 : Mat d)))
        (hA : ∀ i j, Integrable (fun x => (a x • (1 : Mat d)) i j)
          (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x • (1 : Mat d))⁻¹ i j)
          (volume.restrict (originCube 1))),
        (∀ hα' : 0 < α,
          besovCubeNorm (fun x => a x • (1 : Mat d)) hA (α / 2) ξ (half_pos hα') hξ.le < ⊤) ∧
        (α = 0 →
          eLpNorm (fun x => ‖a x • (1 : Mat d)‖) (ENNReal.ofReal ξ)
            (volume.restrict (originCube 1)) < ⊤) ∧
        (∀ hβ' : 0 < β,
          besovCubeNorm (fun x => (a x • (1 : Mat d))⁻¹) hAinv (β / 2) ζ (half_pos hβ')
            hζ.le < ⊤) ∧
        (β = 0 →
          eLpNorm (fun x => ‖(a x • (1 : Mat d))⁻¹‖) (ENNReal.ofReal ζ)
            (volume.restrict (originCube 1)) < ⊤) ∧
        ∃ u : Vec d → ℝ,
          u ∈ Csol (fun x => a x • (1 : Mat d)) (originCube 1) ∧
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 1 ≤ u x) ∧
          eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) = ⊤ ∧
          0 < nonnegativeEssInf (originCube (1 / 2)) u ∧
          nonnegativeEssInf (originCube (1 / 2)) u < ⊤ ∧
          ∀ x : Vec d, |x ⟨0, by omega⟩| < 1 / 2 → (∀ i : Fin d, (i : ℕ) ≠ 0 → x i = 0) →
            ∀ N ∈ 𝓝 x, eLpNorm u ⊤ (volume.restrict (N ∩ originCube 1)) = ⊤ := by
  cases d with
  | zero => omega
  | succ m =>
    have hm : 2 ≤ m := by omega
    obtain ⟨ζ', hζ0, hζ2, hζA, hζB⟩ := exists_cylinderExponent hd (p := ξ) (q := ζ)
      (s := α / 2) (t := β / 2) hξ hζ (by linarith) (by linarith)
      (θ := θ₀) (by rw [hθ₀def]; ring) hθ₀
    let κ := cylinderRadialConstant (m + 1)
    let w := scalarSharpnessWeight (d := m + 1) ζ' κ
    have hκ : 0 < κ := cylinderRadialConstant_pos hd
    have hi := scalarSharpnessWeight_integrable hd hζ0 hζ2 hκ
    obtain ⟨hA, hAinv⟩ := scalarSharpnessCoefficient_entrywise_integrable hd hζ0 hζ2 hκ hi.1 hi.2
    have hApower : ζ' ≤ (m : ℝ) / ξ + 2 * (α / 2) := by
      simpa only [exponentA, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hζA
    have hBpower : 2 - ζ' ≤ (m : ℝ) / ζ + 2 * (β / 2) := by
      simpa only [exponentB, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hζB
    have ha := scalarSharpnessCoefficient_isWeightedCoeffOn hd hζ0 hζ2 hκ
    have hw0 : ∀ x, 0 ≤ w x := fun x => (scalarSharpnessWeight_pos hd hζ0 hζ2 hκ x).le
    have hwm : Measurable w := scalarSharpnessWeight_measurable ζ' κ
    have hV : IsOpenBoundedConvexDomain (originCube (d := m + 1) 1) :=
      CoarseDeGiorgi.Whitney.source_cube_domain (by norm_num)
    have hne : (originCube (d := m + 1) 1).Nonempty :=
      CoarseDeGiorgi.Whitney.source_cube_nonempty (by norm_num)
    obtain ⟨u, Gu, hsol, hdom, hpos, hsup, hinf1, hinf2⟩ :=
      harmonic_replacement_one_plus_dominates hd hV hne ha
        (scalarSubsolutionSum_isWeightedSubsolution hm hζ0 hζ2)
        (Filter.Eventually.of_forall (scalarSubsolutionSum_nonneg hd hζ0 hζ2))
        (scalarSubsolutionSum_large_sets hd hζ0 hζ2)
    refine ⟨w, hwm, scalarSharpnessWeight_pos hd hζ0 hζ2 hκ,
      fun _ _ h => scalarSharpnessWeight_invariant h, ha, hA, hAinv, ?_, ?_, ?_, ?_,
      u, ⟨Gu, hsol⟩, hpos, hsup, hinf1, hinf2, ?_⟩
    · intro hα'
      exact scalarSharpnessWeight_besov hm hζ0 hζ2 hκ hξ.le (half_pos hα') hApower hA
    · intro h0
      have hle : ζ' ≤ (m : ℝ) / ξ := by
        rw [h0] at hApower; simpa using hApower
      exact eLpNorm_scalar_identity_lt_top hw0 (majorant_lp_lt_top hm hζ0 hζ2 hκ
        (by norm_num : (0 : ℝ) < 1) (by norm_num) hξ.le hle w hwm.aestronglyMeasurable hw0
        (scalarSharpnessWeight_majorant hm hζ0 hζ2 hκ))
    · intro hβ'
      exact scalarSharpnessWeight_inv_besov hm hζ0 hζ2 hκ hζ.le (half_pos hβ') hBpower hAinv
    · intro h0
      have hle : 2 - ζ' ≤ (m : ℝ) / ζ := by
        rw [h0] at hBpower; simpa using hBpower
      have heq := scalarWeight_inv_matrix hm hζ0 hζ2 hκ
      change eLpNorm (fun x => ‖(scalarSharpnessWeight (d := m + 1) ζ' κ x • (1 : Mat (m + 1)))⁻¹‖)
        (ENNReal.ofReal ζ) (volume.restrict (originCube 1)) < ⊤
      have heq' : (fun x : Vec (m + 1) =>
          ‖(scalarSharpnessWeight (d := m + 1) ζ' κ x • (1 : Mat (m + 1)))⁻¹‖) =
          fun x => ‖(scalarSharpnessWeight (d := m + 1) ζ' κ x)⁻¹ • (1 : Mat (m + 1))‖ := by
        funext x
        exact congrArg norm (congrFun heq x)
      rw [heq']
      exact eLpNorm_scalar_identity_lt_top
        (fun x => (inv_pos.mpr (scalarSharpnessWeight_pos hd hζ0 hζ2 hκ x)).le)
        (majorant_lp_lt_top hm hζ0 hζ2 hκ (by norm_num : (0 : ℝ) < 2) le_rfl hζ.le hle
          (fun x => (scalarSharpnessWeight (d := m + 1) ζ' κ x)⁻¹)
          (hwm.inv.aestronglyMeasurable)
          (fun x => (inv_pos.mpr (scalarSharpnessWeight_pos hd hζ0 hζ2 hκ x)).le)
          (scalarInvSharpnessWeight_majorant hm hζ0 hζ2 hκ))
    · intro x hx1 hx2 N hN
      have hx0 : x ∈ originCube (d := m + 1) 1 := by
        intro i
        by_cases hi : (i : ℕ) = 0
        · have : i = ⟨0, by omega⟩ := Fin.ext hi
          rw [this]
          have h := abs_lt.mp hx1
          constructor <;> linarith [h.1, h.2]
        · rw [hx2 i hi]
          constructor <;> norm_num
      exact solution_unbounded_near_axis hd hζ0 hζ2 hdom hx0 hx2 hN

end

end CoarseDeGiorgi.SharpnessExamples
