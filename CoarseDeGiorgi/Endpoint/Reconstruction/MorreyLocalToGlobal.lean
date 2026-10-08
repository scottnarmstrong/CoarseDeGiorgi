module

public import CoarseDeGiorgi.Endpoint.Reconstruction.StepInverse
public import CoarseDeGiorgi.Endpoint.Morrey.Cube

/-! # Cellwise Morrey with an Lr estimate for the mean -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem enorm_integralAverage_le_lp {d : ℕ} (Q : TriadicCube d)
    {f : Vec d → ℝ} {r : ℝ} (hr : 1 ≤ r)
    (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet Q))) :
    ‖integralAverage (openCubeSet Q) f‖ₑ ≤
      (volume (openCubeSet Q)) ^ (-(1 / r)) *
        eLpNorm f (ENNReal.ofReal r) (volume.restrict (openCubeSet Q)) := by
  let δ := volume (openCubeSet Q)
  have hδtop : δ ≠ ⊤ := (volume_openCubeSet_lt_top Q).ne
  have hδreal : 0 < δ.toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hδ0 : δ ≠ 0 := (ENNReal.toReal_pos_iff.mp hδreal).1.ne'
  have hL1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (ENNReal.one_le_ofReal.mpr hr) hf
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal (zero_le_one.trans hr),
    div_one, Measure.restrict_apply_univ] at hL1
  have hInt := (enorm_integral_le_lintegral_enorm f).trans_eq
    (eLpNorm_one_eq_lintegral_enorm hf).symm
  have hfactor : δ⁻¹ * δ ^ (1 - 1 / r) = δ ^ (-(1 / r)) := by
    rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hδ0 hδtop]
    congr 1
    ring
  calc
    ‖integralAverage (openCubeSet Q) f‖ₑ = δ⁻¹ *
        ‖∫ x in openCubeSet Q, f x‖ₑ := by
      unfold integralAverage
      rw [enorm_mul, Real.enorm_eq_ofReal_abs,
        abs_of_pos (inv_pos.mpr hδreal), ENNReal.ofReal_inv_of_pos hδreal,
        ENNReal.ofReal_toReal hδtop]
    _ ≤ δ⁻¹ * eLpNorm f 1 (volume.restrict (openCubeSet Q)) := by gcongr
    _ ≤ δ⁻¹ * (eLpNorm f (ENNReal.ofReal r) (volume.restrict (openCubeSet Q)) *
        δ ^ (1 - 1 / r)) := by gcongr
    _ = _ := by rw [mul_left_comm, hfactor, mul_comm]

theorem eLpNorm_top_le_of_local_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (k : ℕ) {f : Vec d → E} {B : ℝ≥0∞}
    (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet Q)))
    (hlocal : ∀ R ∈ descendantsAtDepth Q k,
      eLpNorm f ⊤ (volume.restrict (openCubeSet R)) ≤ B) :
    eLpNorm f ⊤ (volume.restrict (openCubeSet Q)) ≤ B := by
  rw [eLpNorm_exponent_top hf]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  rw [volume_restrict_openCube_eq_sum_descendants Q k, ae_finsetSum_measure_iff]
  intro R hR
  have hfR := hf.mono_measure (Measure.restrict_mono
    (openCubeSet_subset_of_mem_descendantsAtDepth hR) le_rfl)
  have hRbound := hlocal R hR
  rw [eLpNorm_exponent_top hfR] at hRbound
  exact (enorm_ae_le_eLpNormEssSup f (volume.restrict (openCubeSet R))).mono
    fun _ hx => hx.trans hRbound

/-- The local oscillation and local mean bounds use global Lp norms without
any loss from the number of cells. -/
theorem exists_unitCube_cell_morrey_bound {d : ℕ} [NeZero d] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (k : ℕ)
      (u : H1Function (openCubeSet (Homogenization.originCube d 0)))
      (r : ℝ), 1 ≤ r →
      MemLp u.grad (ENNReal.ofReal (2 * d))
        (normalizedCubeMeasure (Homogenization.originCube d 0)) →
      eLpNorm u.toFun ⊤ (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
        (ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℤ))) ^ d)) ^ (-(1 / r)) *
          eLpNorm u.toFun (ENNReal.ofReal r)
            (normalizedCubeMeasure (Homogenization.originCube d 0)) +
        ENNReal.ofReal M * ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)) *
          eLpNorm u.grad (ENNReal.ofReal (2 * d))
            (normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  obtain ⟨M, hM, hmorrey⟩ := Morrey.exists_cube_morrey_bound (d := d)
  refine ⟨M, hM, ?_⟩
  intro k u r hr hgrad
  rw [normalizedCubeMeasure_unit_eq] at hgrad ⊢
  apply eLpNorm_top_le_of_local_le _ k u.memL2.aestronglyMeasurable
  intro R hR
  let uR := u.restrictToOpenSubcube hR
  have hμ : volume.restrict (openCubeSet R) ≤
      volume.restrict (openCubeSet (Homogenization.originCube d 0)) :=
    Measure.restrict_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR) le_rfl
  have hgradR := hgrad.mono_measure hμ
  have hosc := hmorrey R uR hgradR
  have hmean := enorm_integralAverage_le_lp R hr uR.memL2.aestronglyMeasurable
  have hδ0 : volume (openCubeSet R) ≠ 0 := by
    rw [volume_unit_descendant_eq hR]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hμ0 : volume.restrict (openCubeSet R) ≠ 0 := by
    intro h
    have := congrArg (fun μ : Measure (Vec d) => μ Set.univ) h
    apply hδ0
    simpa using this
  calc
    eLpNorm u.toFun ⊤ (volume.restrict (openCubeSet R)) ≤
        eLpNorm (fun x => uR.toFun x - integralAverage (openCubeSet R) uR.toFun) ⊤
          (volume.restrict (openCubeSet R)) + ‖integralAverage (openCubeSet R) uR.toFun‖ₑ := by
      have heq : u.toFun = (fun x => uR.toFun x - integralAverage (openCubeSet R) uR.toFun) +
          (fun _ => integralAverage (openCubeSet R) uR.toFun) := by funext x; simp [uR]
      conv_lhs => rw [heq]
      simpa only [eLpNorm_const _ (by simp : (⊤ : ℝ≥0∞) ≠ 0) hμ0,
        ENNReal.toReal_top, div_zero, ENNReal.rpow_zero, mul_one] using
        eLpNorm_add_le (μ := volume.restrict (openCubeSet R)) (f := fun x => uR.toFun x - integralAverage (openCubeSet R) uR.toFun)
          (g := fun _ => integralAverage (openCubeSet R) uR.toFun) le_top
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal ((cubeScaleFactor R) ^ (1 / 2 : ℝ)) *
        eLpNorm u.grad (ENNReal.ofReal (2 * d)) (volume.restrict (openCubeSet R)) +
        (volume (openCubeSet R)) ^ (-(1 / r)) *
          eLpNorm u.toFun (ENNReal.ofReal r) (volume.restrict (openCubeSet R)) :=
      add_le_add hosc hmean
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal ((cubeScaleFactor R) ^ (1 / 2 : ℝ)) *
        eLpNorm u.grad (ENNReal.ofReal (2 * d))
          (volume.restrict (openCubeSet (Homogenization.originCube d 0))) +
        (volume (openCubeSet R)) ^ (-(1 / r)) *
          eLpNorm u.toFun (ENNReal.ofReal r)
            (volume.restrict (openCubeSet (Homogenization.originCube d 0))) := by
      gcongr
    _ = _ := by
      rw [cubeScaleFactor_descendant hR, cubeScaleFactor_originCube, zpow_zero,
        one_mul, volume_unit_descendant_eq hR, add_comm]

end

end CoarseDeGiorgi.Endpoint.Reconstruction
