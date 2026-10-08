import CoarseDeGiorgi.Foundations.Reconstruction.ProjectionL1
import Homogenization.Besov.Duality.ProjectedPairing.Averages

/-! # Nesting and parent-cell cancellation for triadic projections -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Reaveraging a finer scalar projection gives the original parent projection. -/
theorem cubeProjection_nesting (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet Q) volume) :
    cubeProjection Q j (cubeProjection Q (j + 1) f) = cubeProjection Q j f := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
    exact cubeAverage_cubeProjection_succ_eq_cubeAverage_of_mem_descendantsAtDepth_of_integrableOn
      f hR (hf.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR))
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet _ _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet _ _ _ hx]

/-- Each finer-minus-parent increment has zero ordinary integral on every parent cell. -/
theorem integral_cubeProjection_increment_eq_zero {Q R : TriadicCube d} {j : ℕ}
    (f : Vec d → ℝ) (hR : R ∈ descendantsAtDepth Q j)
    (hf : IntegrableOn f (cubeSet Q) volume) :
    ∫ x in cubeSet R, (cubeProjection Q (j + 1) f x - cubeProjection Q j f x)
      ∂volume = 0 := by
  have hnext := cubeAverage_cubeProjection_succ_eq_cubeAverage_of_mem_descendantsAtDepth_of_integrableOn
    f hR (hf.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR))
  have hparent := cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR
  have heq : (∫ x in cubeSet R, cubeProjection Q (j + 1) f x ∂volume) =
      ∫ x in cubeSet R, cubeProjection Q j f x ∂volume := by
    exact mul_left_cancel₀ (inv_ne_zero (cubeVolume_pos R).ne') (hnext.trans hparent.symm)
  rw [integral_sub
    (integrableOn_cubeProjection_succ_of_mem_descendantsAtDepth f hR)
    ((integrableOn_cubeProjection_of_integrableOn Q j f).mono_set
      (cubeSet_subset_of_mem_descendantsAtDepth hR)), heq, sub_self]

/-- Coordinatewise vector projection, on the usual half-open triadic grid. -/
def cubeProjectionVec (Q : TriadicCube d) (j : ℕ) (f : Vec d → Vec d) (x : Vec d) : Vec d :=
  fun i => cubeProjection Q j (fun y => f y i) x

theorem cubeProjectionVec_eq_cubeAverageVec_of_mem {Q R : TriadicCube d} {j : ℕ}
    (f : Vec d → Vec d) (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ cubeSet R) : cubeProjectionVec Q j f x = cubeAverageVec R f := by
  funext i
  exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth (fun y => f y i) hR hx

theorem cubeProjectionVec_nesting (Q : TriadicCube d) (j : ℕ) (f : Vec d → Vec d)
    (hf : IntegrableOn f (cubeSet Q) volume) :
    cubeProjectionVec Q j (cubeProjectionVec Q (j + 1) f) = cubeProjectionVec Q j f := by
  funext x i
  exact congrFun (cubeProjection_nesting Q j (fun y => f y i) ((ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).integrable_comp hf)) x

theorem integral_cubeProjectionVec_increment_coordinate_eq_zero {Q R : TriadicCube d} {j : ℕ}
    (f : Vec d → Vec d) (hR : R ∈ descendantsAtDepth Q j)
    (hf : IntegrableOn f (cubeSet Q) volume) (i : Fin d) :
    ∫ x in cubeSet R, (cubeProjectionVec Q (j + 1) f x i - cubeProjectionVec Q j f x i)
      ∂volume = 0 :=
  integral_cubeProjection_increment_eq_zero (fun y => f y i) hR ((ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).integrable_comp hf)

end

end CoarseDeGiorgi.Foundations.Reconstruction
