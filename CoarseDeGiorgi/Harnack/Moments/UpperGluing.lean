import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
import CoarseDeGiorgi.LowerFractional.CompactCover
import CoarseDeGiorgi.Weighted.UpperSpecMinimum
import CoarseDeGiorgi.Weighted.UpperSpecHarmonic
import CoarseDeGiorgi.Whitney.LiftCell
import CoarseDeGiorgi.Whitney.LiftSums
import CoarseDeGiorgi.Whitney.LiftZeroExtension

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem upper_gluing_quadratic {d : ℕ} [NeZero d] (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) (e : Vec d) :
    vecDot e (matVecMul (upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        vecDot e (matVecMul (upperResponseOnCell k a ha η) e)) /
        ((triangulation (d := d) k).card : ℝ) := by
  classical
  let V := originCube (d := d) 1
  have hV : IsOpenBoundedConvexDomain V := LowerFractional.lower_unitCube_domain
  have hne : V.Nonempty := LowerFractional.lower_unitCube_nonempty
  have hvol : volume V = 1 := Assembly.ClassicalMomentsImpl.originCube_volume_one d
  let cellPair (η : SimplexIndex d k) :=
    Whitney.liftCellPair (simplexCell_isOpenBoundedConvexDomain k η)
      (simplexCell_nonempty k η) (weightedCoeffOn_simplexCell k a ha η) e
  let corrVal (η : SimplexIndex d k) := (cellPair η).1 - Weighted.responseAffine e
  let corrGrad (η : SimplexIndex d k) := (cellPair η).2 - (fun _ => e)
  let liftedVal (η : SimplexIndex d k) := (simplexCell k η).indicator (corrVal η)
  let liftedGrad (η : SimplexIndex d k) := (simplexCell k η).indicator (corrGrad η)
  have hcellPair (η : SimplexIndex d k) :
      IsWeightedSolution a (simplexCell k η) (cellPair η).1 (cellPair η).2 ∧
      MemH1a0 a (simplexCell k η) (corrVal η) (corrGrad η) := by
    simpa only [cellPair, corrVal, corrGrad] using
      Whitney.liftCellPair_spec (simplexCell_isOpenBoundedConvexDomain k η)
        (simplexCell_nonempty k η) (weightedCoeffOn_simplexCell k a ha η) e
  have hExt (η : SimplexIndex d k) :
      MemH1a0 a V (liftedVal η) (liftedGrad η) := by
    exact Whitney.lift_zero_extension (simplexCell_isOpenBoundedConvexDomain k η)
      (simplexCell_nonempty k η) hV.isOpen
      (CoarseDeGiorgi.simplexCell_subset_originCube k η) ha (hcellPair η).2
  let valSum : Vec d → ℝ := ∑ η : SimplexIndex d k, liftedVal η
  let gradSum : Vec d → Vec d := ∑ η : SimplexIndex d k, liftedGrad η
  have hsum_on_cell (η : SimplexIndex d k) {x : Vec d}
      (hx : x ∈ simplexCell k η) : gradSum x = corrGrad η x := by
    classical
    dsimp only [gradSum]
    rw [Finset.sum_apply]
    ext i
    rw [Finset.sum_eq_single η]
    · simp only [liftedGrad, Set.indicator_of_mem hx]
    · intro θ hθ hθη
      have hdis := Assembly.ClassicalMomentsImpl.simplexCell_pairwise_disjoint k
        (show η ≠ θ from Ne.symm hθη)
      have hxθ : x ∉ simplexCell k θ := by
        intro hxθ
        exact (Set.disjoint_left.mp hdis hx) hxθ
      simp only [liftedGrad]
      rw [Set.indicator_of_notMem hxθ]
    · intro hη
      simp at hη
  let valWhole : Vec d → ℝ := Weighted.responseAffine e + valSum
  let gradWhole : Vec d → Vec d := (fun _ => e) + gradSum
  have hcorrection : MemH1a0 a V valSum gradSum := by
    simpa [valSum, gradSum] using
      Whitney.lift_boundary_finset_sum hV hne ha liftedVal liftedGrad hExt Finset.univ
  have hbaseline : MemH1a a V (Weighted.responseAffine e) (fun _ => e) :=
    Weighted.responseAffine_memH1a hV ha e
  have hwhole : MemH1a a V valWhole gradWhole := by
    change MemH1a a V (Weighted.responseAffine e + valSum)
      ((fun _ => e) + gradSum)
    exact Weighted.MemH1a.add hV hne ha hbaseline
      (Weighted.MemH1a0.memH1a ha hcorrection)
  have hboundary : MemH1a0 a V
      (fun x => valWhole x - Weighted.responseAffine e x)
      (fun x => gradWhole x - e) := by
    convert hcorrection using 1 <;> funext x <;>
      simp only [valWhole, gradWhole, Pi.add_apply] <;> abel
  have hquad_cell (η : SimplexIndex d k) {x : Vec d}
      (hx : x ∈ simplexCell k η) :
      vecDot (gradWhole x) (matVecMul (a x) (gradWhole x)) =
        vecDot ((cellPair η).2 x) (matVecMul (a x) ((cellPair η).2 x)) := by
    change vecDot (e + gradSum x) (matVecMul (a x) (e + gradSum x)) = _
    rw [hsum_on_cell η hx]
    have hgrad : e + corrGrad η x = (cellPair η).2 x := by
      simp [corrGrad]
    rw [hgrad]
  let energyWhole : Vec d → ℝ := fun x =>
    vecDot (gradWhole x) (matVecMul (a x) (gradWhole x))
  have hEnergyInt : IntegrableOn energyWhole V :=
    Weighted.quadratic_integrable ha hwhole.2.1
      (Weighted.MemH1a.energy_lt_top hV.isOpen ha hwhole)
  have hcellAverage (η : SimplexIndex d k) :
      volumeAverage (simplexCell k η) energyWhole =
        volumeAverage (simplexCell k η)
          (fun x => vecDot ((cellPair η).2 x)
            (matVecMul (a x) ((cellPair η).2 x))) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem
      (simplexCell_isOpenBoundedConvexDomain k η).isOpen.measurableSet] with x hx
    exact hquad_cell η hx
  have hcellResponse (η : SimplexIndex d k) :
      vecDot e (matVecMul (upperResponseOnCell k a ha η) e) =
        volumeAverage (simplexCell k η)
          (fun x => vecDot ((cellPair η).2 x)
            (matVecMul (a x) ((cellPair η).2 x))) := by
    have hboundaryη : MemH1a0 a (simplexCell k η)
        (fun x => (cellPair η).1 x - (vecDot e x + 0))
        (fun x => (cellPair η).2 x - e) := by
      have hval : (fun x => (cellPair η).1 x - (vecDot e x + 0)) = corrVal η := by
        funext x
        dsimp [corrVal]
        rw [show vecDot e x = Weighted.responseAffine e x from rfl]
        ring
      have hgrad : (fun x => (cellPair η).2 x - e) = corrGrad η := by
        funext x
        rfl
      rw [hval, hgrad]
      exact (hcellPair η).2
    exact Weighted.UpperResponseImpl.upper_affine_energy
      (simplexCell_isOpenBoundedConvexDomain k η) (simplexCell_nonempty k η)
      (weightedCoeffOn_simplexCell k a ha η) e 0 (hcellPair η).1 hboundaryη
  have hwholeAverage : volumeAverage V energyWhole =
      ((triangulation (d := d) k).attach.sum fun η =>
        vecDot e (matVecMul (upperResponseOnCell k a ha η) e)) /
        ((triangulation (d := d) k).card : ℝ) := by
    have hp := Assembly.ClassicalMomentsImpl.partition_average k hEnergyInt
    have hc : volumeAverage V energyWhole = ∫ x in V, energyWhole x := by
      simp [volumeAverage, hvol]
    rw [hc, ← hp]
    congr 1
    apply Finset.sum_congr rfl
    intro η hη
    rw [hcellAverage η, (hcellResponse η).symm]
  have hmin := Weighted.UpperResponseImpl.upper_affine_minimum hV hne ha e
  have hleast := hmin.2 ⟨valWhole, gradWhole, hwhole, hboundary, rfl⟩
  calc
    _ ≤ volumeAverage V energyWhole := hleast
    _ = _ := hwholeAverage

/-- As quadratic forms, the upper response on the unit cube is at most the average of the
cellwise upper responses at level `k`. -/
theorem upper_gluing {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) (e : Vec d) :
    vecDot e (matVecMul (upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        vecDot e (matVecMul (upperResponseOnCell k a ha η) e)) /
        ((triangulation (d := d) k).card : ℝ) := by
  exact @upper_gluing_quadratic d ⟨by omega⟩ k a ha e

end CoarseDeGiorgi.Harnack.Moments
