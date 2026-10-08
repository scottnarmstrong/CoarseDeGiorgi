module

public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import CoarseDeGiorgi.Statements.SimplexCellNonempty
public import CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
public import CoarseDeGiorgi.Statements.Triangulation
public import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell
public import CoarseDeGiorgi.LowerFractional.CompactCover
public import CoarseDeGiorgi.LowerFractional.Restriction
public import CoarseDeGiorgi.Weighted.LowerSpecNorm

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem lowerResponse_quadratic_le_cellAverage {d : ℕ} [NeZero d]
    (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (e : Vec d) :
    vecDot e (matVecMul (lowerResponseInv a (originCube 1)
        (LowerFractional.lower_unitCube_domain) (LowerFractional.lower_unitCube_nonempty) ha) e) ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        vecDot e (matVecMul (lowerResponseInvOnCell k a ha η) e)) /
          ((triangulation (d := d) k).card : ℝ) := by
  classical
  let V := originCube (d := d) 1
  let N : ℝ := ((triangulation (d := d) k).card : ℝ)
  have hV : IsOpenBoundedConvexDomain V := LowerFractional.lower_unitCube_domain
  have hne : V.Nonempty := LowerFractional.lower_unitCube_nonempty
  have hvol : volume V = 1 := Assembly.ClassicalMomentsImpl.originCube_volume_one d
  let obj (G : Vec d → Vec d) : Vec d → ℝ := fun x =>
    -vecDot (G x) (matVecMul (a x) (G x)) + 2 * vecDot e (G x)
  have hobj_int {w : Vec d → ℝ} {G : Vec d → Vec d}
      (hw : MemH1a a V w G) : IntegrableOn (obj G) V := by
    have hE : IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) V :=
      Weighted.quadratic_integrable ha hw.2.1
        (Weighted.MemH1a.energy_lt_top hV.isOpen ha hw)
    have hG := Weighted.GradientCore.integrable ha
      (Weighted.memH1aEnergyField hV.isOpen ha hw)
    have hD : IntegrableOn (fun x => vecDot e (G x)) V := by
      change Integrable (fun x => vecDot e (G x)) (volume.restrict V)
      simpa only [Function.comp_def, Weighted.lowerDot_apply,
        Weighted.memH1aEnergyField_field] using (Weighted.lowerDot e).integrable_comp hG
    have heq : obj G =
        (fun x => -vecDot (G x) (matVecMul (a x) (G x))) +
          (fun x => 2 * vecDot e (G x)) := by
      funext x
      rfl
    rw [heq]
    exact hE.neg.add (hD.const_mul 2)
  have hobj_avg {w : Vec d → ℝ} {G : Vec d → Vec d}
      (hw : MemH1a a V w G) :
      volumeAverage V (obj G) =
        ((triangulation (d := d) k).attach.sum fun η =>
          volumeAverage (simplexCell k η) (obj G)) / N := by
    have hp := Assembly.ClassicalMomentsImpl.partition_average k (hobj_int hw)
    have hc : volumeAverage V (obj G) = ∫ x in V, obj G x := by
      simp [volumeAverage, hvol]
    rw [hc, ← hp]
  have hcell_obj {w : Vec d → ℝ} {G : Vec d → Vec d}
      (hw : MemH1a a V w G) (η : SimplexIndex d k) :
      volumeAverage (simplexCell k η) (obj G) ≤
        vecDot e (matVecMul (lowerResponseInvOnCell k a ha η) e) := by
    have hηV := simplexCell_isOpenBoundedConvexDomain k η
    have hηne := simplexCell_nonempty k η
    have hηsub : simplexCell k η ⊆ V := by
      exact CoarseDeGiorgi.simplexCell_subset_originCube k η
    have hηa := weightedCoeffOn_simplexCell k a ha η
    have hηw : MemH1a a (simplexCell k η) w G :=
      LowerFractional.memH1a_restrict hV hne ha hηV hηsub hw
    have hE : IntegrableOn
        (fun x => vecDot (G x) (matVecMul (a x) (G x))) (simplexCell k η) :=
      Weighted.quadratic_integrable hηa hηw.2.1
        (Weighted.MemH1a.energy_lt_top hηV.isOpen hηa hηw)
    have hG := Weighted.GradientCore.integrable hηa
      (Weighted.memH1aEnergyField hηV.isOpen hηa hηw)
    have hD : IntegrableOn (fun x => vecDot e (G x)) (simplexCell k η) := by
      change Integrable (fun x => vecDot e (G x)) (volume.restrict (simplexCell k η))
      simpa only [Function.comp_def, Weighted.lowerDot_apply,
        Weighted.memH1aEnergyField_field] using (Weighted.lowerDot e).integrable_comp hG
    have heq : volumeAverage (simplexCell k η) (obj G) =
        -volumeAverage (simplexCell k η)
            (fun x => vecDot (G x) (matVecMul (a x) (G x))) +
          2 * vecDot e (volumeAverageVec (simplexCell k η) G) := by
      have hf : obj G =
          (fun x => -vecDot (G x) (matVecMul (a x) (G x))) +
            (fun x => 2 * vecDot e (G x)) := by
        funext x
        rfl
      calc
        volumeAverage (simplexCell k η) (obj G) =
            volumeAverage (simplexCell k η)
              ((fun x => -vecDot (G x) (matVecMul (a x) (G x))) +
                (fun x => 2 * vecDot e (G x))) := by rw [hf]
        _ = volumeAverage (simplexCell k η) (fun x =>
              -vecDot (G x) (matVecMul (a x) (G x))) +
            volumeAverage (simplexCell k η) (fun x => 2 * vecDot e (G x)) :=
          volumeAverage_add hE.neg (hD.const_mul 2)
        _ = (-1 : ℝ) * volumeAverage (simplexCell k η)
              (fun x => vecDot (G x) (matVecMul (a x) (G x))) +
            2 * volumeAverage (simplexCell k η) (fun x => vecDot e (G x)) := by
          rw [show (fun x => -vecDot (G x) (matVecMul (a x) (G x))) =
                (-1 : ℝ) • (fun x => vecDot (G x) (matVecMul (a x) (G x))) by
              funext x; simp]
          rw [show (fun x => 2 * vecDot e (G x)) =
                (2 : ℝ) • (fun x => vecDot e (G x)) by
              funext x; rfl]
          rw [volumeAverage_smul, volumeAverage_smul]
        _ = -volumeAverage (simplexCell k η)
              (fun x => vecDot (G x) (matVecMul (a x) (G x))) +
            2 * vecDot e (volumeAverageVec (simplexCell k η) G) := by
          rw [volumeAverage_vecDot_left e G
            (Weighted.memH1a_memW11 hηV hηne hηa hηw).2.1]
          change (-1 : ℝ) * volumeAverage (simplexCell k η)
                (fun x => vecDot (G x) (matVecMul (a x) (G x))) +
              2 * vecDot e (fun i => volumeAverage (simplexCell k η) (fun x => G x i)) =
            -volumeAverage (simplexCell k η)
                (fun x => vecDot (G x) (matVecMul (a x) (G x))) +
              2 * vecDot e (fun i => volumeAverage (simplexCell k η) (fun x => G x i))
          ring
    have htest' : volumeAverage (simplexCell k η) (obj G) ≤
        vecDot e (matVecMul (lowerResponseInvOnCell k a ha η) e) := by
      have hsup := Weighted.LowerResponseImpl.lowerResponseInv_all_functions hηV hηne hηa e
      have hle :
          ((volumeAverage (simplexCell k η)
            (fun x => -vecDot (G x) (matVecMul (a x) (G x)) + 2 * vecDot e (G x)) : ℝ) : EReal) ≤
            ((vecDot e (matVecMul (Weighted.LowerResponseImpl.lowerResponseInv a
              (simplexCell k η) hηV hηne hηa) e) : ℝ) : EReal) := by
        rw [hsup]
        exact le_iSup_of_le w (le_iSup_of_le G (le_iSup_of_le hηw le_rfl))
      have hresp : lowerResponseInv a (simplexCell k η) hηV hηne hηa =
          Weighted.LowerResponseImpl.lowerResponseInv a (simplexCell k η) hηV hηne hηa := rfl
      have hleReal : volumeAverage (simplexCell k η) (obj G) ≤
          vecDot e (matVecMul (lowerResponseInv a (simplexCell k η) hηV hηne hηa) e) := by
        rw [hresp]
        exact EReal.coe_le_coe_iff.mp hle
      exact heq ▸ hleReal
    exact htest'
  have hobj_bound {w : Vec d → ℝ} {G : Vec d → Vec d}
      (hw : MemH1a a V w G) :
      volumeAverage V (obj G) ≤
        ((triangulation (d := d) k).attach.sum fun η =>
          vecDot e (matVecMul (lowerResponseInvOnCell k a ha η) e)) / N := by
    rw [hobj_avg hw]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro η hη
    exact hcell_obj hw η
  have hsup := Weighted.LowerResponseImpl.lowerResponseInv_all_functions hV hne ha e
  have hleSup : (⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
      (_ : MemH1a a V w G),
      ((volumeAverage V (obj G) : ℝ) : EReal)) ≤
      (((triangulation (d := d) k).attach.sum fun η =>
        vecDot e (matVecMul (lowerResponseInvOnCell k a ha η) e)) / N : ℝ) := by
    apply iSup_le
    intro w
    apply iSup_le
    intro G
    apply iSup_le
    intro hw
    exact EReal.coe_le_coe_iff.mpr (hobj_bound hw)
  rw [← hsup] at hleSup
  exact EReal.coe_le_coe_iff.mp hleSup

/-- The inverse lower response norm on the unit cube is at most the average, over level-`k`
simplices, of the cellwise inverse lower response norms. -/
theorem lower_whole_cube_aggregation {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    ‖lowerResponseInv a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        ‖lowerResponseInvOnCell k a ha η‖) /
          ((triangulation (d := d) k).card : ℝ) := by
  classical
  let M : ℝ := ((triangulation (d := d) k).attach.sum fun η =>
    ‖lowerResponseInvOnCell k a ha (show SimplexIndex d k from η)‖) /
      ((triangulation (d := d) k).card : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (Finset.sum_nonneg fun η hη => norm_nonneg _)
      (Nat.cast_nonneg _)
  have hq (e : Vec d) :
      vecDot e (matVecMul (lowerResponseInv a (originCube 1)
          LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) ≤
        M * vecNormSq e := by
    have hagg := @lowerResponse_quadratic_le_cellAverage d
      ⟨by omega⟩ k a ha e
    have hagg' :
        vecDot e (matVecMul (lowerResponseInv a (originCube 1)
          LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) ≤
          ((triangulation (d := d) k).attach.sum fun η =>
            vecDot e (matVecMul
              (lowerResponseInvOnCell k a ha (show SimplexIndex d k from η)) e)) /
            ((triangulation (d := d) k).card : ℝ) := by
      exact hagg
    calc
      _ ≤ ((triangulation (d := d) k).attach.sum fun η =>
          vecDot e (matVecMul
            (lowerResponseInvOnCell k a ha (show SimplexIndex d k from η)) e)) /
            ((triangulation (d := d) k).card : ℝ) := hagg
      _ ≤ ((triangulation (d := d) k).attach.sum fun η =>
          ‖lowerResponseInvOnCell k a ha (show SimplexIndex d k from η)‖ * vecNormSq e) /
            ((triangulation (d := d) k).card : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro η hη
        exact Weighted.LowerResponseImpl.lower_quadratic_le_norm
          (lowerResponseInvOnCell k a ha (show SimplexIndex d k from η)) e
      _ = M * vecNormSq e := by
        dsimp [M]
        rw [div_eq_mul_inv, ← Finset.sum_mul]
        ring
  let S : Mat d := M • (1 : Mat d)
  have hS (e : Vec d) : vecDot e (matVecMul S e) = M * vecNormSq e := by
    simp [S, vecDot, matVecMul, vecNormSq, Matrix.one_apply]
    change (∑ i, e i * (M * e i)) = M * ∑ i, e i * e i
    calc
      (∑ i, e i * (M * e i)) = ∑ i, M * (e i * e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = M * ∑ i, e i * e i := by rw [Finset.mul_sum]
  have hnorm := Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic
    (A := lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha)
    (B := S)
    (Weighted.LowerResponseImpl.lowerResponseInv_posDef
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha).posSemidef
    (fun e => (hq e).trans_eq (hS e).symm)
  have hnormS : ‖S‖ = M := by
    change ‖M • (1 : Mat d)‖ = M
    rw [norm_smul, show ‖(M : ℝ)‖ = M from abs_of_nonneg hM]
    have hOne : ‖(1 : Mat d)‖ = 1 := by
      rw [Matrix.cstar_norm_def]
      have hclm : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Mat d) =
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
        ext x
        simp [Matrix.toEuclideanCLM]
      rw [hclm]
      apply le_antisymm ContinuousLinearMap.norm_id_le
      let i : Fin d := ⟨0, by omega⟩
      let x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (basisVec i)
      have hx : ‖x‖ ≠ 0 := by
        simp [x, basisVec]
      have hid :=
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))).ratio_le_opNorm x
      rw [ContinuousLinearMap.id_apply, div_self hx] at hid
      exact hid
    rw [hOne]
    ring
  change ‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ ≤ M
  exact hnorm.trans_eq hnormS

end CoarseDeGiorgi.Harnack.Moments
