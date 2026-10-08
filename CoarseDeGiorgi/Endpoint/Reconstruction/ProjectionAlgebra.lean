module

public import CoarseDeGiorgi.Endpoint.Reconstruction.DirichletAlgebra

/-! # Linearity and finite telescopes of fine averages -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem cubeProjectionVec_sub {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (F G : Vec d → Vec d) (hF : IntegrableOn F (cubeSet Q))
    (hG : IntegrableOn G (cubeSet Q)) :
    Foundations.Reconstruction.cubeProjectionVec Q k (fun x => F x - G x) =
      fun x => Foundations.Reconstruction.cubeProjectionVec Q k F x -
        Foundations.Reconstruction.cubeProjectionVec Q k G x := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    rw [Foundations.Reconstruction.cubeProjectionVec_eq_cubeAverageVec_of_mem _ hR hxR,
      Foundations.Reconstruction.cubeProjectionVec_eq_cubeAverageVec_of_mem _ hR hxR,
      Foundations.Reconstruction.cubeProjectionVec_eq_cubeAverageVec_of_mem _ hR hxR]
    funext i
    simp only [cubeAverageVec, cubeAverage, Pi.sub_apply]
    rw [integral_sub ((hF.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)).eval i)
      ((hG.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)).eval i)]
    ring
  · funext i
    simp only [Foundations.Reconstruction.cubeProjectionVec, Pi.sub_apply,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q k _ hx, sub_zero]

theorem integrableOn_unit_cubeSet {d : ℕ} {F : Vec d → Vec d}
    (hF : IntegrableOn F (CoarseDeGiorgi.originCube 1)) :
    IntegrableOn F (cubeSet (Homogenization.originCube d 0)) := by
  rw [IntegrableOn, Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _),
    ← originCube_one_eq_openCubeSet]
  exact hF

theorem fineAverage_sub_ae {d : ℕ} (k : ℕ) (F G : Vec d → Vec d)
    (hF : IntegrableOn F (CoarseDeGiorgi.originCube 1))
    (hG : IntegrableOn G (CoarseDeGiorgi.originCube 1)) :
    fineAverage k (fun x => F x - G x) =ᵐ[volume]
      fun x => fineAverage k F x - fineAverage k G x := by
  filter_upwards [fineAverage_eq_cubeProjectionVec_ae k (fun x => F x - G x),
    fineAverage_eq_cubeProjectionVec_ae k F, fineAverage_eq_cubeProjectionVec_ae k G] with x hsub hfx hgx
  rw [hsub, hfx, hgx, cubeProjectionVec_sub _ _ _ _
    (integrableOn_unit_cubeSet hF) (integrableOn_unit_cubeSet hG)]

theorem fineIncrement_sub_ae {d : ℕ} (k : ℕ) (F G : Vec d → Vec d)
    (hF : IntegrableOn F (CoarseDeGiorgi.originCube 1))
    (hG : IntegrableOn G (CoarseDeGiorgi.originCube 1)) :
    fineIncrement k (fun x => F x - G x) =ᵐ[volume]
      fun x => fineIncrement k F x - fineIncrement k G x := by
  filter_upwards [fineAverage_sub_ae (k + 1) F G hF hG,
    fineAverage_sub_ae k F G hF hG] with x hn hk
  simp only [fineIncrement, hn, hk]
  abel

theorem cubeAverageVec_eq_volumeAverageVec_open {d : ℕ} (Q : TriadicCube d)
    (G : Vec d → Vec d) : cubeAverageVec Q G = volumeAverageVec (openCubeSet Q) G := by
  funext i
  change cubeAverage Q (fun x => G x i) = volumeAverage (openCubeSet Q) (fun x => G x i)
  exact cubeAverage_eq_integralAverage Q _

theorem fineAverage_zero_ae_of_average_zero {d : ℕ} (G : Vec d → Vec d)
    (hmean : volumeAverageVec (CoarseDeGiorgi.originCube 1) G = 0) :
    fineAverage 0 G =ᵐ[volume.restrict (CoarseDeGiorgi.originCube 1)] fun _ => 0 := by
  have hQ : Homogenization.originCube d 0 ∈ descendantsAtDepth (Homogenization.originCube d 0) 0 := by simp
  rw [originCube_one_eq_openCubeSet]
  filter_upwards [(fineAverage_eq_cubeProjectionVec_ae 0 G).restrict,
    ae_restrict_mem (isOpen_openCubeSet (Homogenization.originCube d 0)).measurableSet] with x hx hxQ
  rw [hx, Foundations.Reconstruction.cubeProjectionVec_eq_cubeAverageVec_of_mem G hQ
    (openCubeSet_subset_cubeSet _ hxQ), cubeAverageVec_eq_volumeAverageVec_open,
    ← originCube_one_eq_openCubeSet, hmean]

theorem blockPartialSum_equation {d : ℕ} (w : ℕ → UnitH10 d)
    (G : Vec d → Vec d)
    (hw : ∀ k : ℕ, 1 ≤ k → UnitDirichletEquation (w k) (fineIncrement (k - 1) G))
    (N : ℕ) : UnitDirichletEquation (blockPartialSum w N)
      (fun x => fineAverage N G x - fineAverage 0 G x) := by
  induction N with
  | zero =>
    intro ψ
    change (∫ x in openCubeSet (Homogenization.originCube d 0),
      vecDot (matVecMul (1 : Mat d) (0 : Vec d)) (ψ.toH1Function.grad x)) = _
    simp only [matVecMul_one, vecDot_zero_left, sub_self, integral_zero]
  | succ n ih =>
    have hfine (k : ℕ) : MemVectorL2 (openCubeSet (Homogenization.originCube d 0))
        (fineAverage k G) := (memLp_fineAverage k G 2).mono_measure Measure.restrict_le_self
    have hinc : MemVectorL2 (openCubeSet (Homogenization.originCube d 0))
        (fineIncrement n G) := (memLp_fineIncrement n G 2).mono_measure Measure.restrict_le_self
    have hstep := hw (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hstep
    rw [blockPartialSum]
    apply (ih.add hstep ((hfine n).sub (hfine 0)) hinc).congr_forcing
    exact Filter.Eventually.of_forall fun x => by dsimp [fineIncrement]; abel

theorem average_gradient_h10_eq_zero {d : ℕ} (u : UnitH10 d) :
    volumeAverageVec (CoarseDeGiorgi.originCube 1) u.toH1Function.grad = 0 := by
  let U := openCubeSet (Homogenization.originCube d 0)
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet _).isFiniteMeasure_restrict_volume
  have hi := IsPotentialZeroTraceOn.integral_eq_zero u.isPotentialZeroTraceOn
  rw [originCube_one_eq_openCubeSet]
  funext i
  simp only [volumeAverageVec, volumeAverage, Pi.zero_apply]
  rw [show (∫ x in openCubeSet (Homogenization.originCube d 0), u.toH1Function.grad x i) = 0 from
    congrFun hi i, mul_zero]

end

end CoarseDeGiorgi.Endpoint.Reconstruction
