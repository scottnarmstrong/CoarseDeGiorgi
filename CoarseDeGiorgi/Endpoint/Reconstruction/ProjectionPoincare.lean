module

public import CoarseDeGiorgi.Endpoint.Reconstruction.LocalPoincare
public import CoarseDeGiorgi.Endpoint.Reconstruction.PartitionLp

/-! # Scale-sharp Poincaré for a triadic projection residual -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem cubeAverage_eq_integralAverage {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q f = integralAverage (openCubeSet Q) f := by
  unfold cubeAverage integralAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet, volume_openCubeSet_toReal]

theorem cubeScaleFactor_descendant {d : ℕ} {Q R : TriadicCube d} {k : ℕ}
    (hR : R ∈ descendantsAtDepth Q k) :
    cubeScaleFactor R = cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ)) := by
  unfold cubeScaleFactor
  rw [scale_eq_sub_of_mem_descendantsAtDepth hR, sub_eq_add_neg,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

theorem cubeProjection_eq_integralAverage_on_cell_ae {d : ℕ} {Q R : TriadicCube d}
    {k : ℕ} (hR : R ∈ descendantsAtDepth Q k) (f : Vec d → ℝ) :
    cubeProjection Q k f =ᵐ[volume.restrict (openCubeSet R)]
      fun _ => integralAverage (openCubeSet R) f := by
  filter_upwards [ae_restrict_mem (isOpen_openCubeSet R).measurableSet] with x hx
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR
    (openCubeSet_subset_cubeSet R hx), cubeAverage_eq_integralAverage]

/-- Local Poincaré glues across the partition with no dependence on the
number of cells. Every gradient coordinate may be dominated by one common
`L^p` function, as when applying the estimate to a Hessian row. -/
theorem exists_projection_residual_bound {d : ℕ} [NeZero d] (p : FiniteLpExponent) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d) (k : ℕ)
      (u : W1pFunction (openCubeSet Q) p.exponent) (g : Vec d → ℝ),
      MemLp g p.exponent (volume.restrict (openCubeSet Q)) →
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (openCubeSet Q), ‖u.grad x i‖ ≤ ‖g x‖) →
      eLpNorm (fun x => u.toFun x - cubeProjection Q k u.toFun x) p.exponent
          (volume.restrict (openCubeSet Q)) ≤
        ENNReal.ofReal (C * cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ))) *
          eLpNorm g p.exponent (volume.restrict (openCubeSet Q)) := by
  classical
  obtain ⟨C, hC, hPoincare⟩ := exists_cube_subAverage_poincare_finite (d := d) p
  refine ⟨C * d, mul_nonneg hC (Nat.cast_nonneg _), ?_⟩
  intro Q k u g hg hdom
  have hproj : AEStronglyMeasurable (cubeProjection Q k u.toFun)
      (volume.restrict (openCubeSet Q)) := by
    have h := (integrableOn_cubeProjection_of_integrableOn Q k u.toFun).aestronglyMeasurable
    rwa [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)] at h
  apply eLpNorm_cube_le_of_local_le Q k
    (f := fun x => u.toFun x - cubeProjection Q k u.toFun x) (g := g)
    (ne_of_gt (zero_lt_one.trans p.one_lt))
    p.lt_top.ne (u.memLp.aestronglyMeasurable.sub hproj) hg.aestronglyMeasurable
  intro R hR
  have hRQ : openCubeSet R ⊆ openCubeSet Q := openCubeSet_subset_of_mem_descendantsAtDepth hR
  let uR := u.restrict (isOpen_openCubeSet R) hRQ
  have hgR := hg.mono_measure (Measure.restrict_mono hRQ le_rfl)
  have hcoord (i : Fin d) : uR.gradCoordLpSeminorm i ≤
      (eLpNorm g p.exponent (volume.restrict (openCubeSet R))).toReal := by
    apply ENNReal.toReal_mono hgR.eLpNorm_ne_top
    apply eLpNorm_mono_ae (uR.grad_memLp i).aestronglyMeasurable
    exact (hdom i).filter_mono (ae_mono (Measure.restrict_mono hRQ le_rfl))
  have hsum : uR.gradientCoordLpSeminormSum ≤
      d * (eLpNorm g p.exponent (volume.restrict (openCubeSet R))).toReal :=
    (Finset.sum_le_sum fun i _ => hcoord i).trans_eq (by simp)
  have heq : (fun x => u.toFun x - cubeProjection Q k u.toFun x)
      =ᵐ[volume.restrict (openCubeSet R)]
        fun x => uR.toFun x - integralAverage (openCubeSet R) uR.toFun := by
    filter_upwards [cubeProjection_eq_integralAverage_on_cell_ae hR u.toFun] with x hx
    rw [hx]
    rfl
  rw [eLpNorm_congr_ae heq]
  refine (hPoincare R uR).trans ?_
  calc
    ENNReal.ofReal (C * cubeScaleFactor R * uR.gradientCoordLpSeminormSum) ≤
        ENNReal.ofReal (C * cubeScaleFactor R *
          (d * (eLpNorm g p.exponent (volume.restrict (openCubeSet R))).toReal)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum (by
        have : 0 < cubeScaleFactor R := zpow_pos (by norm_num) _
        positivity))
    _ = _ := by
      rw [cubeScaleFactor_descendant hR]
      have hfactor : C * (cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ))) *
          (d * (eLpNorm g p.exponent (volume.restrict (openCubeSet R))).toReal) =
          ((C * d) * cubeScaleFactor Q * (3 : ℝ) ^ (-(k : ℤ))) *
            (eLpNorm g p.exponent (volume.restrict (openCubeSet R))).toReal := by ring
      rw [hfactor, ENNReal.ofReal_mul (by
        have : 0 < cubeScaleFactor Q := zpow_pos (by norm_num) _
        positivity), ENNReal.ofReal_toReal hgR.eLpNorm_ne_top]

end

end CoarseDeGiorgi.Endpoint.Reconstruction
