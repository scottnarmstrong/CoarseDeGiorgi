module

public import CoarseDeGiorgi.Weighted.LowerSpecMean
public import CoarseDeGiorgi.Weighted.UpperSpecHarmonic
public import CoarseDeGiorgi.Weighted.ResponseBoundsLower
public import CoarseDeGiorgi.LowerFractional.CompactCover
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.UpperResponse
public import CoarseDeGiorgi.Statements.LowerResponseInv
public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- As quadratic forms, the inverse upper response is below the inverse lower response. -/
theorem inverse_response_order_quadratic {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    ∀ e : Vec d,
      vecDot e (matVecMul ((CoarseDeGiorgi.upperResponse a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha)⁻¹) e) ≤
        vecDot e (matVecMul (CoarseDeGiorgi.lowerResponseInv a (originCube 1)
          LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) := by
  classical
  have hnz : NeZero d := ⟨by omega⟩
  let V := CoarseDeGiorgi.originCube (d := d) 1
  let hV : IsOpenBoundedConvexDomain V := LowerFractional.lower_unitCube_domain
  let hne : V.Nonempty := LowerFractional.lower_unitCube_nonempty
  let A := Weighted.UpperResponseImpl.upperResponse a V hV hne ha
  let B := Weighted.LowerResponseImpl.lowerResponseInv a V hV hne ha
  have hvol : volume V = 1 := Assembly.ClassicalMomentsImpl.originCube_volume_one d
  have hA : A.PosDef := Weighted.UpperResponseImpl.upperResponse_posDef hV hne ha
  have htrial (e ξ : Vec d) :
      -vecDot ξ (matVecMul A ξ) + 2 * vecDot e ξ ≤ vecDot e (matVecMul B e) := by
    obtain ⟨h, Gh, hh, hb⟩ :=
      Weighted.UpperResponseImpl.upper_affine_replacement hV hne ha ξ 0
    have hbase : (fun x => vecDot ξ x + 0) = Weighted.responseAffine ξ := by
      funext x
      change vecDot ξ x + 0 = vecDot ξ x
      ring
    have hbMean : MemH1a0 a V
        (h - Weighted.responseAffine ξ) (Gh - fun _ => ξ) := by
      convert hb using 1
      · funext x
        change h x - Weighted.responseAffine ξ x = h x - (vecDot ξ x + 0)
        rw [hbase.symm]
    have hmean : volumeAverageVec V Gh = ξ := by
      funext i
      have hi := congrFun (Weighted.upper_harmonic_integral hV hne ha ξ hh hbMean) i
      have hW11 := @Weighted.memH1a_memW11 d V a hnz hV hne ha h Gh hh.1
      have hGint : Integrable Gh (volume.restrict V) := Integrable.of_eval hW11.2.1
      let L : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
      have hcoord : (∫ x in V, Gh x) i = ∫ x in V, Gh x i := by
        simpa only [L, ContinuousLinearMap.proj_apply] using
          (ContinuousLinearMap.integral_comp_comm L hGint).symm
      have hi' : ∫ x in V, Gh x i = ξ i := by
        calc
          _ = (∫ x in V, Gh x) i := hcoord.symm
          _ = ((volume V).toReal • ξ) i := hi
          _ = ξ i := by simp [hvol]
      change volumeAverage V (fun x => Gh x i) = ξ i
      simp [volumeAverage, hvol, hi']
    have henergy := Weighted.UpperResponseImpl.upper_affine_energy hV hne ha ξ 0 hh hb
    have henergy' : volumeAverage V
        (fun x => vecDot (Gh x) (matVecMul (a x) (Gh x))) =
          vecDot ξ (matVecMul A ξ) := by
      simpa only [A] using henergy.symm
    have hscalar := @Weighted.LowerResponseImpl.lowerResponseInv_scalar_test d V a hnz
      hV hne ha h Gh hh.1 e 1
    rw [henergy', hmean] at hscalar
    nlinarith [hscalar]
  intro e
  let ξ : Vec d := matVecMul A⁻¹ e
  have hlin := htrial e ξ
  have hcomplete := Weighted.lower_square_completion A hA e ξ
  have hopt :
      -vecDot ξ (matVecMul A ξ) + 2 * vecDot e ξ =
        vecDot e (matVecMul A⁻¹ e) := by
    simpa [ξ, vecDot, matVecMul, Matrix.mulVec, dotProduct] using hcomplete
  rw [hopt] at hlin
  simpa [A, B, V, hV, hne, Weighted.UpperResponseImpl.upperResponse,
    Weighted.LowerResponseImpl.lowerResponseInv, CoarseDeGiorgi.upperResponse,
    CoarseDeGiorgi.lowerResponseInv] using hlin

end CoarseDeGiorgi.Harnack.Moments
