import Homogenization.CoarseGraining.Definitions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

/-! Corollary D (`c.classical.moments`): parameter arithmetic and Jensen in the Euclidean
operator norm. The contrast `paramTheta` is written explicitly rather than imported. -/

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The pure-parameter converse, in the exact range of the statement. -/
theorem classical_moments_converse :
    ∀ d : ℕ, 3 ≤ d → ∀ p q : ℝ,
      1 < p → 1 < q →
      ∀ s t : ℝ, 0 < s → 0 < t →
        0 < 1 - s - t - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) →
          1 / p + 1 / q < 2 / ((d : ℝ) - 1) := by
  intro d hd p q _hp _hq s t hs ht hθ
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) - 1 := by linarith only [hd3]
  apply (lt_div_iff₀ hdpos).mpr
  nlinarith only [hs, ht, hθ]

/-- Jensen's inequality for a finite, nonzero-volume cell and the scoped L² operator norm. -/
theorem classical_matrix_moment_jensen {d : ℕ} {V : Set (Vec d)}
    {A : Vec d → Mat d} {p : ℝ} (hp : 1 ≤ p)
    (hV0 : volume V ≠ 0) (hVfinite : volume V ≠ ⊤)
    (hA : IntegrableOn A V)
    (hAp : IntegrableOn (fun x => ‖A x‖ ^ p) V) :
    ‖⨍ x in V, A x‖ ^ p ≤ ⨍ x in V, ‖A x‖ ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hc : ConvexOn ℝ (Set.univ : Set (Mat d)) (fun B => ‖B‖ ^ p) := by
    refine ⟨convex_univ, ?_⟩
    intro B hB C hC s t hs ht hst
    have hn := (convexOn_norm (E := Mat d) convex_univ).2 hB hC hs ht hst
    have hr := (convexOn_rpow hp).2 (norm_nonneg B) (norm_nonneg C) hs ht hst
    exact (Real.rpow_le_rpow (norm_nonneg _) hn hp0).trans hr
  exact hc.map_set_average_le
    ((Real.continuous_rpow_const hp0).comp continuous_norm).continuousOn isClosed_univ hV0 hVfinite
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hA hAp

/-- The entrywise average used by the response bounds is the Bochner matrix average. -/
theorem classical_matrix_average_eq {d : ℕ} {V : Set (Vec d)}
    {A : Vec d → Mat d} (hA : IntegrableOn A V) :
    volumeAverageMat V A = ⨍ x in V, A x := by
  ext i j
  let L : Mat d →L[ℝ] ℝ :=
    (show Mat d →ₗ[ℝ] ℝ from
      { toFun := fun B => B i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toContinuousLinearMap
  have hi := L.integral_comp_comm hA
  change (∫ x in V, A x i j) = (∫ x in V, A x) i j at hi
  rw [setAverage_eq]
  change (volume V).toReal⁻¹ * (∫ x in V, A x i j) =
    (volume V).toReal⁻¹ * (∫ x in V, A x) i j
  rw [hi]

/-- The source's cellwise Jensen inequality, using its entrywise matrix average. -/
theorem classical_matrix_moment_bound {d : ℕ} {V : Set (Vec d)}
    {A : Vec d → Mat d} {p : ℝ} (hp : 1 ≤ p)
    (hV0 : volume V ≠ 0) (hVfinite : volume V ≠ ⊤)
    (hA : IntegrableOn A V)
    (hAp : IntegrableOn (fun x => ‖A x‖ ^ p) V) :
    ‖volumeAverageMat V A‖ ^ p ≤ volumeAverage V (fun x => ‖A x‖ ^ p) := by
  rw [classical_matrix_average_eq hA]
  have h := classical_matrix_moment_jensen hp hV0 hVfinite hA hAp
  simpa only [setAverage_eq, measureReal_def, smul_eq_mul, volumeAverage] using h


end CoarseDeGiorgi.Weighted
