module

public import CoarseDeGiorgi.Endpoint.Reconstruction.WeightedBlocks
public import CoarseDeGiorgi.Endpoint.Reconstruction.ProjectionAlgebra
public import CoarseDeGiorgi.Weighted.PairOperations

/-! # Continuity of each Dirichlet block in weighted energy -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section

theorem tendsto_dirichlet_block_difference {d : ℕ} [NeZero d]
    {q : ℝ} (hq : 1 < q) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d} (hv : MemH1a0 a (CoarseDeGiorgi.originCube 1) v G)
    (f : ℕ → Vec d → ℝ) (H : ℕ → Vec d → Vec d)
    (hf : ∀ j, MemH1a0 a (CoarseDeGiorgi.originCube 1) (f j) (H j))
    (he : Tendsto (fun j => weightedEnergy a (CoarseDeGiorgi.originCube 1) (H j - G)) atTop (𝓝 0))
    (k : ℕ) (w : UnitH10 d) (wj : ℕ → UnitH10 d)
    (hw : UnitDirichletEquation w (fineIncrement k G))
    (hwj : ∀ j, UnitDirichletEquation (wj j) (fineIncrement k (H j))) :
    Tendsto (fun j => eLpNorm ((wj j).toH1Function.toFun - w.toH1Function.toFun)
      (ENNReal.ofReal (paramR q)) (volume.restrict (CoarseDeGiorgi.originCube 1))) atTop (𝓝 0) := by
  let U := CoarseDeGiorgi.originCube (d := d) 1
  let μ := volume.restrict U
  have hU := LowerFractional.lower_unitCube_domain (d := d)
  have hne := LowerFractional.lower_unitCube_nonempty (d := d)
  have hr1 := LowerFractional.lower_paramR_gt_one hq
  have hr2 : paramR q < 2 := by
    unfold paramR
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hrs : (paramR q).HolderConjugate (paramR q / (paramR q - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hr1).mpr rfl
  obtain ⟨C, hC, hcancel⟩ := exists_unitCube_dirichlet_cancellation_bound (d := d) hrs hr2
  have hμ : normalizedCubeMeasure (Homogenization.originCube d 0) = μ := by
    rw [normalizedCubeMeasure_unit_eq, ← originCube_one_eq_openCubeSet]
  have hG : IntegrableOn G U := Integrable.of_eval
    (Weighted.memH1a_memW11 hU hne ha (Weighted.MemH1a0.memH1a ha hv)).2.1
  have hH (j : ℕ) : IntegrableOn (H j) U := Integrable.of_eval
    (Weighted.memH1a_memW11 hU hne ha (Weighted.MemH1a0.memH1a ha (hf j))).2.1
  let K := ENNReal.ofReal (C * (3 : ℝ) ^ (-(k : ℤ))) * 2 *
    (ENNReal.ofReal (lowerCellAverage a ha (k + 1) q)) ^ (1 / (2 * q))
  have hK : K ≠ ⊤ := by
    dsimp [K]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
    · exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top).ne
  have hb (j : ℕ) : eLpNorm ((wj j).toH1Function.toFun - w.toH1Function.toFun)
      (ENNReal.ofReal (paramR q)) μ ≤ K * (weightedEnergy a U (H j - G)) ^ (1 / 2 : ℝ) := by
    have hdiff := (hwj j).sub hw
      ((memLp_fineIncrement k (H j) 2).mono_measure Measure.restrict_le_self)
      ((memLp_fineIncrement k G 2).mono_measure Measure.restrict_le_self)
    have hdiff' : UnitDirichletEquation (wj j - w) (fineIncrement k (H j - G)) :=
      hdiff.congr_forcing ((fineIncrement_sub_ae k (H j) G (hH j) hG).symm.restrict)
    have hnorm := hcancel k (fineIncrement k (H j - G))
      (by rw [hμ]; exact (memLp_fineIncrement k (H j - G) _).mono_measure Measure.restrict_le_self)
      (fun R hR => integral_fineIncrement_coordinate_eq_zero k (H j - G) ((hH j).sub hG) hR)
      (wj j - w) hdiff'
    rw [hμ, h10_sub_toFun] at hnorm
    have hdata := (eLpNorm_field_le_euclidNorm
      ((memLp_fineIncrement k (H j - G) (ENNReal.ofReal (paramR q))).aestronglyMeasurable.restrict)).trans
      (fine_increment_weighted_norm_le k a ha (Weighted.MemH1a0.sub hU hne ha (hf j) hv) hq)
    refine hnorm.trans ?_
    calc
      _ ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(k : ℤ))) *
        (2 * (ENNReal.ofReal (lowerCellAverage a ha (k + 1) q)) ^ (1 / (2 * q)) *
          (weightedEnergy a U (H j - G)) ^ (1 / 2 : ℝ)) := by
            gcongr
            simpa only [μ, U, mul_assoc, ENNReal.rpow_eq_pow] using hdata
      _ = _ := by dsimp [K]; ring
  have hroot : Tendsto (fun j => (weightedEnergy a U (H j - G)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [U, Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp he
  have hscaled := ENNReal.Tendsto.const_mul (a := K) hroot (Or.inr hK)
  simp only [mul_zero] at hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled (fun _ => bot_le) hb

end
end CoarseDeGiorgi.Endpoint.Reconstruction
