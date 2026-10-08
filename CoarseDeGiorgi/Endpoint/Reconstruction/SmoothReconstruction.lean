import CoarseDeGiorgi.Endpoint.Reconstruction.SmoothProjection
import CoarseDeGiorgi.Endpoint.Reconstruction.EnergyBound

/-! # Finite Dirichlet reconstruction for bounded H10 gradients -/

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem tendsto_dirichlet_blockPartialSum_of_bounded_gradient {d : ℕ} [NeZero d]
    (u : UnitH10 d) (w : ℕ → UnitH10 d)
    (hw : ∀ k : ℕ, 1 ≤ k → UnitDirichletEquation (w k) (fineIncrement (k - 1) u.toH1Function.grad))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ cubeSet (Homogenization.originCube d 0), ‖u.toH1Function.grad x‖ ≤ B)
    {r : ℝ} (_hr : 1 ≤ r) (hr2 : r ≤ 2) :
    Tendsto (fun N => eLpNorm (fun x => u.toH1Function.toFun x -
      ∑ k ∈ Finset.Icc 1 N, (w k).toH1Function.toFun x) (ENNReal.ofReal r)
      (volume.restrict (CoarseDeGiorgi.originCube 1))) atTop (𝓝 0) := by
  let Q := Homogenization.originCube d 0
  let U := openCubeSet Q
  let μ := volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)
  have hμ : volume.restrict U = μ := by
    dsimp [μ, U, Q]
    rw [originCube_one_eq_openCubeSet]
  let : IsFiniteMeasure (volume.restrict U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hG : IntegrableOn u.toH1Function.grad (CoarseDeGiorgi.originCube 1) := by
    rw [originCube_one_eq_openCubeSet]
    exact u.toH1Function.grad_memVectorL2.integrable (by norm_num)
  have hprojection := tendsto_eLpNorm_fineAverage_sub_hilbert_two_of_bound
    u.toH1Function.grad hG hB hbound
  obtain ⟨C, hC, henergy⟩ := exists_dirichlet_value_l2_bound (d := d)
  have hzero := fineAverage_zero_ae_of_average_zero u.toH1Function.grad
    (average_gradient_h10_eq_zero u)
  have hres (N : ℕ) : UnitDirichletEquation (u - blockPartialSum w N)
      (fun x => u.toH1Function.grad x - fineAverage N u.toH1Function.grad x) := by
    have hu : UnitDirichletEquation u u.toH1Function.grad := by
      intro ψ
      simp only [matVecMul_one]
    have hpartial := blockPartialSum_equation w u.toH1Function.grad hw N
    have hpartial' : UnitDirichletEquation (blockPartialSum w N) (fineAverage N u.toH1Function.grad) :=
      hpartial.congr_forcing (by
        rw [hμ]
        exact hzero.mono fun x hx => by dsimp only; rw [hx, sub_zero])
    exact hu.sub hpartial' u.toH1Function.grad_memVectorL2
      ((memLp_fineAverage N u.toH1Function.grad 2).mono_measure Measure.restrict_le_self)
  have h2 (N : ℕ) : eLpNorm (u - blockPartialSum w N).toH1Function.toFun 2 μ ≤
      ENNReal.ofReal C * eLpNorm
        (fun x => HilbertVec.ofVec (fineAverage N u.toH1Function.grad x - u.toH1Function.grad x)) 2 μ := by
    have hF : MemVectorL2 U
        (fun x => u.toH1Function.grad x - fineAverage N u.toH1Function.grad x) :=
      u.toH1Function.grad_memVectorL2.sub
        ((memLp_fineAverage N u.toH1Function.grad 2).mono_measure Measure.restrict_le_self)
    have hh := henergy _ hF (u - blockPartialSum w N) (hres N)
    rw [hμ] at hh
    have heq : hilbertifyVecField (fun x => u.toH1Function.grad x - fineAverage N u.toH1Function.grad x) =
        -(fun x => HilbertVec.ofVec (fineAverage N u.toH1Function.grad x - u.toH1Function.grad x)) := by
      funext x
      change WithLp.toLp 2 _ = -WithLp.toLp 2 _
      rw [← WithLp.toLp_neg]
      congr 1
      abel_nf
    simpa only [heq, eLpNorm_neg] using hh
  have hD := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hprojection (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hD
  have ht2 : Tendsto (fun N => eLpNorm (u - blockPartialSum w N).toH1Function.toFun 2 μ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD (fun _ => bot_le) h2
  have hmass : μ Set.univ = 1 := by
    have hunit := normalizedCubeMeasure_unit_eq (d := d)
    rw [← hμ]
    exact hunit ▸ normalizedCubeMeasure_apply_univ Q
  have hsmall (N : ℕ) : eLpNorm (u - blockPartialSum w N).toH1Function.toFun (ENNReal.ofReal r) μ ≤
      eLpNorm (u - blockPartialSum w N).toH1Function.toFun 2 μ := by
    have hm : AEStronglyMeasurable (u - blockPartialSum w N).toH1Function.toFun μ := by
      rw [← hμ]
      exact (u - blockPartialSum w N).toH1Function.memL2.aestronglyMeasurable
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (by exact (ENNReal.ofReal_le_ofReal hr2).trans_eq (by norm_num) : ENNReal.ofReal r ≤ 2) hm
    simpa only [hmass, ENNReal.one_rpow, mul_one] using hb
  have ht := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht2 (fun _ => bot_le) hsmall
  simpa only [h10_sub_toFun, blockPartialSum_toFun] using ht

end

end CoarseDeGiorgi.Endpoint.Reconstruction
