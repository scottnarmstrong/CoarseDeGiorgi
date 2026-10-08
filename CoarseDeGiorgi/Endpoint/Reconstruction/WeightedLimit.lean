import CoarseDeGiorgi.Endpoint.Reconstruction.FiniteContinuity
import CoarseDeGiorgi.Endpoint.Reconstruction.WeightedApproximation
import CoarseDeGiorgi.Endpoint.Reconstruction.SmoothInput
import CoarseDeGiorgi.Endpoint.Reconstruction.SmoothTail

/-! # Reconstruction of weighted zero-trace representatives by density -/
namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section

theorem weighted_reconstruction_converges {d : ℕ} [NeZero d] {q : ℝ} (hq : 1 < q)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (C : ℝ)
    (hblocks : ∀ (f : Vec d → ℝ) (H : Vec d → Vec d),
      MemH1a0 a (CoarseDeGiorgi.originCube 1) f H →
      ∃ W : ℕ → UnitH10 d, ∀ k : ℕ, 1 ≤ k →
        UnitDirichletEquation (W k) (fineIncrement (k - 1) H) ∧
        eLpNorm (W k).toH1Function.toFun (ENNReal.ofReal (paramR q))
          (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
            ENNReal.ofReal C * blockCost a ha q k *
              (weightedEnergy a (CoarseDeGiorgi.originCube 1) H) ^ (1 / 2 : ℝ))
    {v : Vec d → ℝ} {G : Vec d → Vec d} (hv : MemH1a0 a (CoarseDeGiorgi.originCube 1) v G)
    (w : ℕ → UnitH10 d)
    (hw : ∀ k : ℕ, 1 ≤ k → UnitDirichletEquation (w k) (fineIncrement (k - 1) G))
    (hc : ∑' k, blockCost a ha q k ≠ ⊤) :
    Tendsto (fun N => eLpNorm (fun x => v x - ∑ k ∈ Finset.Icc 1 N, (w k).toH1Function.toFun x)
      (ENNReal.ofReal (paramR q)) (volume.restrict (CoarseDeGiorgi.originCube 1))) atTop (𝓝 0) := by
  let U := CoarseDeGiorgi.originCube (d := d) 1
  let μ := volume.restrict U
  let r := ENNReal.ofReal (paramR q)
  let c := blockCost a ha q
  let E := (weightedEnergy a U G) ^ (1 / 2 : ℝ)
  have hr1 : 1 ≤ r := ENNReal.one_le_ofReal.mpr (LowerFractional.lower_paramR_gt_one hq).le
  have hr2 : paramR q ≤ 2 := by
    unfold paramR
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hU := LowerFractional.lower_unitCube_domain (d := d)
  have hne := LowerFractional.lower_unitCube_nonempty (d := d)
  have hμ : volume.restrict (openCubeSet (Homogenization.originCube d 0)) = μ := by
    rw [← originCube_one_eq_openCubeSet]
  have hwm (k : ℕ) : AEStronglyMeasurable (w k).toH1Function.toFun μ := by
    rw [← hμ]
    exact (w k).toH1Function.memL2.aestronglyMeasurable
  obtain ⟨f, hL, hdiff, henergy⟩ := exists_smooth_energy_approximation a ha hv
  have hf (j : ℕ) := smooth_unit_memH1a0 a ha (f j)
  choose W hW using fun j => hblocks (f j).val (smoothGrad (f j).val) (hf j)
  have hWm (j k : ℕ) : AEStronglyMeasurable (W j k).toH1Function.toFun μ := by
    rw [← hμ]
    exact (W j k).toH1Function.memL2.aestronglyMeasurable
  have hsmooth (j : ℕ) : Tendsto (fun N => eLpNorm
      (fun x => (f j).val x - ∑ k ∈ Finset.Icc 1 N, (W j k).toH1Function.toFun x) r μ) atTop (𝓝 0) := by
    obtain ⟨B, hB, hb⟩ := smooth_unit_gradient_bounded (f j)
    have ht := tendsto_dirichlet_blockPartialSum_of_bounded_gradient
      (smoothUnitH10 (f j)) (W j) (by simpa only [smoothUnitH10_grad] using fun k hk => (hW j k hk).1)
      hB (by simpa only [smoothUnitH10_grad] using hb)
      (LowerFractional.lower_paramR_gt_one hq).le hr2
    simpa only [smoothUnitH10_toFun] using ht
  have htail (j N : ℕ) : eLpNorm
      (fun x => (f j).val x - ∑ k ∈ Finset.Icc 1 N, (W j k).toH1Function.toFun x) r μ ≤
      ENNReal.ofReal C * blockTail c N * (weightedEnergy a U (smoothGrad (f j).val)) ^ (1 / 2 : ℝ) :=
    reconstruction_tail_bound hr1 (f j).property.1.continuous.aestronglyMeasurable.restrict
      (fun k => (W j k).toH1Function.toFun) (hWm j) c (ENNReal.ofReal C) _
      (fun k hk => (hW j k hk).2) (hsmooth j) N
  have hres (N : ℕ) : eLpNorm
      (fun x => v x - ∑ k ∈ Finset.Icc 1 N, (w k).toH1Function.toFun x) r μ ≤
      ENNReal.ofReal C * blockTail c N * E := by
    have hfixed (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : Tendsto
        (fun j => eLpNorm ((W j k).toH1Function.toFun - (w k).toH1Function.toFun) r μ) atTop (𝓝 0) :=
      tendsto_dirichlet_block_difference hq a ha hv (fun j => (f j).val)
        (fun j => smoothGrad (f j).val) hf hdiff (k - 1) (w k) (fun j => W j k)
        (hw k (Finset.mem_Icc.mp hk).1) (fun j => (hW j k (Finset.mem_Icc.mp hk).1).1)
    have hfinite := tendsto_eLpNorm_finset_sum_sub hr1 (Finset.Icc 1 N)
      (fun j k => (W j k).toH1Function.toFun) (fun k => (w k).toH1Function.toFun) hfixed
    have hsumMeas (j : ℕ) : AEStronglyMeasurable
        ((∑ k ∈ Finset.Icc 1 N, (W j k).toH1Function.toFun) - ∑ k ∈ Finset.Icc 1 N, (w k).toH1Function.toFun) μ :=
      (Finset.aestronglyMeasurable_sum _ (fun k _ => hWm j k)).sub
        (Finset.aestronglyMeasurable_sum _ (fun k _ => hwm k))
    have hfiniteL1 := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfinite
      (fun _ => bot_le) (fun j => unit_l1_le_lp hr1 (hsumMeas j))
    have hconv : Tendsto (fun j => eLpNorm
        ((fun x => (f j).val x - ∑ k ∈ Finset.Icc 1 N, (W j k).toH1Function.toFun x) -
          (fun x => v x - ∑ k ∈ Finset.Icc 1 N, (w k).toH1Function.toFun x)) 1 μ) atTop (𝓝 0) := by
      have ht := Weighted.tendsto_l1_add hL (Weighted.tendsto_l1_neg hfiniteL1)
      convert ht using 1
      funext j
      congr 1
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Finset.sum_apply]
      ring
    have hm (j : ℕ) : AEStronglyMeasurable
        (fun x => (f j).val x - ∑ k ∈ Finset.Icc 1 N, (W j k).toH1Function.toFun x) μ :=
      (f j).property.1.continuous.aestronglyMeasurable.restrict.sub
        (by simpa only [Finset.sum_fn] using Finset.aestronglyMeasurable_sum (Finset.Icc 1 N) (fun k _ => hWm j k))
    have hvm : AEStronglyMeasurable (fun x => v x - ∑ k ∈ Finset.Icc 1 N, (w k).toH1Function.toFun x) μ :=
      hv.1.sub (by simpa only [Finset.sum_fn] using Finset.aestronglyMeasurable_sum (Finset.Icc 1 N) (fun k _ => hwm k))
    have hB := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C * blockTail c N)
      henergy (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (blockTail_ne_top hc N)))
    exact Morrey.eLpNorm_le_of_tendstoInMeasure_bound hm hvm
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) hconv) hB (fun j => htail j N)
  have hE : E ≠ ⊤ := by
    apply (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _).ne
    exact (Weighted.memH1a_memW11 hU hne ha (Weighted.MemH1a0.memH1a ha hv)).2.2.2.2.ne
  have hK := ENNReal.mul_ne_top (a := ENNReal.ofReal C) (b := E) ENNReal.ofReal_ne_top hE
  have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C * E) (tendsto_blockTail hc) (Or.inr hK)
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
  intro N
  exact (hres N).trans_eq (by ring)

end
end CoarseDeGiorgi.Endpoint.Reconstruction
