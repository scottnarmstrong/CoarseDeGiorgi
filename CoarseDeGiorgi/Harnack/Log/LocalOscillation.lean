import CoarseDeGiorgi.LowerFractional.MeanCube
import CoarseDeGiorgi.LowerFractional.CubeDomain
import CoarseDeGiorgi.Harnack.Log.FiniteCover
import CoarseDeGiorgi.Foundations.Reconstruction.Representatives
import CoarseDeGiorgi.LowerFractional.Restriction
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.LowerFractionalBound
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.WeightedEnergy

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- On every auxiliary cube `auxCube m z`, the `Lʳ` oscillation about the mean is bounded by
`C 3^(-mα)` times the fractional seminorm, with `C` independent of `m`, `z` and `w`. -/
theorem centered_auxCube_fractional_bound {d : ℕ} [NeZero d] {α r : ℝ}
    (hr : 1 ≤ r) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ),
        AEStronglyMeasurable w (volume.restrict (auxCube m z)) →
        IntegrableOn w (auxCube m z) →
        eLpNorm (fun x => w x - volumeAverage (auxCube m z) w)
          (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-(m : ℝ) * α)) *
            fracSeminorm (auxCube m z) α r w := by
  obtain ⟨C, hC, hmean⟩ :=
    LowerFractional.fractional_mean_norm_auxCube (d := d) hr hα
  refine ⟨C, hC, ?_⟩
  intro m z w hw hwi
  let Q := auxCube m z
  let c := volumeAverage Q w
  let wc : Vec d → ℝ := fun x => w x - c
  let : IsFiniteMeasure (volume.restrict Q) :=
    (LowerFractional.auxCube_isOpenBoundedConvexDomain m z).isFiniteMeasure_restrict_volume
  have hwc : AEStronglyMeasurable wc (volume.restrict Q) := by
    exact hw.sub aestronglyMeasurable_const
  have hvol : (volume Q).toReal ≠ 0 := by
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨Foundations.Reconstruction.volume_auxCube_ne_zero m z,
      Foundations.Reconstruction.volume_auxCube_ne_top m z⟩
  have hmean0 : volumeAverage Q wc = 0 := by
    change volumeAverage (auxCube m z)
      (w - fun _ => volumeAverage (auxCube m z) w) = 0
    rw [volumeAverage_sub hwi (integrable_const _), volumeAverage_const hvol]
    simp
  have hfrac : fracSeminorm Q α r wc = fracSeminorm Q α r w := by
    simpa only [wc, sub_eq_add_neg, Foundations.Reconstruction.fracSeminorm_eq_statement] using
      Foundations.Reconstruction.fracSeminorm_add_const Q α r (-c) w
  have h := hmean m z wc hwc
  simpa [Q, wc, hmean0, hfrac] using h

/-- The lower fractional estimate (`p.lower.fractional`) converts the logarithm's weighted energy
bound on `15/16` into a local Lʳ oscillation estimate on each fixed covering
cube. -/
theorem log_local_oscillation_of_energy_bound {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ Cmean Cfrac : ℝ, 0 < Cmean ∧ 0 < Cfrac ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
        (_hrange : spatialMomentRange a ha p q s t)
        (w : Vec d → ℝ) (G : Vec d → Vec d)
        (_hw : MemH1a a (originCube 1) w G)
        (E : ℝ≥0∞)
        (_henergy : weightedEnergy a (originCube (15 / 16 : ℝ)) G ≤ E),
        ∀ z ∈ fixedLogGrid (d := d),
          eLpNorm (fun x => w x - volumeAverage (auxCube 4 z) w)
            (ENNReal.ofReal (paramR q)) (volume.restrict (auxCube 4 z)) ≤
            ENNReal.ofReal (Cmean * (3 : ℝ) ^ (-(4 : ℝ) * alphaParam t)) *
              ENNReal.ofReal Cfrac *
              ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2) *
              ENNReal.rpow E (1 / 2) := by
  have : NeZero d := ⟨by omega⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hthetaExpr := hθ
  unfold paramTheta at hthetaExpr
  have hcoef : 0 < ((d : ℝ) - 1) / 2 * (1 / p + 1 / q) := by
    have hdreal : 1 < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
    positivity
  have htlt : t < 1 := by nlinarith [hthetaExpr, hs, hcoef]
  have hα : 0 ≤ alphaParam t := by
    unfold alphaParam
    linarith
  have hr : 1 ≤ paramR q := by
    dsimp [paramR]
    rw [le_div_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  obtain ⟨Cmean, hCmean, hmean⟩ :=
    centered_auxCube_fractional_bound (d := d) hr hα
  obtain ⟨Cfrac, hCfrac, hfrac⟩ :=
    CoarseDeGiorgi.lower_fractional_bound d hd q t hq ht
  refine ⟨Cmean, Cfrac, hCmean, hCfrac, ?_⟩
  intro a ha hrange w G hw E henergy z hz
  have hcube : originCube (d := d) 1 = auxCube 1 (fun _ : Fin d => 0) := by
    ext x
    simp [originCube, auxCube, sub_self, sub_zero, Int.cast_zero, zero_mul, abs_lt]
  have hV : IsOpenBoundedConvexDomain (originCube (d := d) 1) := by
    rw [hcube]
    exact LowerFractional.auxCube_isOpenBoundedConvexDomain (d := d) 1 (fun _ => 0)
  have hne : (originCube (d := d) 1).Nonempty := by
    rw [hcube]
    exact LowerFractional.auxCube_nonempty (d := d) 1 (fun _ => 0)
  have hQdomain : IsOpenBoundedConvexDomain (auxCube 4 z) :=
    LowerFractional.auxCube_isOpenBoundedConvexDomain 4 z
  have hQne : (auxCube 4 z).Nonempty := LowerFractional.auxCube_nonempty 4 z
  have hQ15 : closure (auxCube 4 z) ⊆ originCube (15 / 16 : ℝ) :=
    fixedLogGrid_closure_inside hz
  have h151 : originCube (15 / 16 : ℝ) ⊆ originCube (d := d) 1 := by
    intro x hx i
    have hxi := hx i
    change -(15 / 16 / 2 : ℝ) < x i ∧ x i < 15 / 16 / 2 at hxi
    change -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2
    constructor <;> nlinarith
  have hQ1 : closure (auxCube 4 z) ⊆ originCube (d := d) 1 := hQ15.trans h151
  have hQsub : auxCube 4 z ⊆ originCube (d := d) 1 := subset_closure.trans hQ1
  have hQsubset15 : auxCube 4 z ⊆ originCube (15 / 16 : ℝ) :=
    subset_closure.trans hQ15
  have haQ := LowerFractional.weightedCoeffOn_mono ha hQsub
  have hwQ := LowerFractional.memH1a_restrict hV hne ha hQdomain hQsub hw
  have hW11 := Weighted.memH1a_memW11 hQdomain hQne haQ hwQ
  have hwInt : IntegrableOn w (auxCube 4 z) := hW11.1
  have hsemi := hfrac p s hp hs a ha hrange 4 z w G hQsub hwQ
  have henergyQ : weightedEnergy a (auxCube 4 z) G ≤ E :=
    (LowerFractional.weightedEnergy_mono hQsubset15 G).trans henergy
  have hmeanbound := hmean 4 z w hwQ.1 hwInt
  have hroot := ENNReal.rpow_le_rpow henergyQ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ ENNReal.ofReal (Cmean * (3 : ℝ) ^ (-(4 : ℝ) * alphaParam t)) *
          fracSeminorm (auxCube 4 z) (alphaParam t) (paramR q) w := hmeanbound
    _ ≤ ENNReal.ofReal (Cmean * (3 : ℝ) ^ (-(4 : ℝ) * alphaParam t)) *
          (ENNReal.ofReal Cfrac *
            ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2) *
            ENNReal.rpow (weightedEnergy a (auxCube 4 z) G) (1 / 2)) :=
          mul_le_mul_right hsemi _
    _ = (ENNReal.ofReal (Cmean * (3 : ℝ) ^ (-(4 : ℝ) * alphaParam t)) *
          ENNReal.ofReal Cfrac *
          ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2)) *
          ENNReal.rpow (weightedEnergy a (auxCube 4 z) G) (1 / 2) := by ac_rfl
    _ ≤ (ENNReal.ofReal (Cmean * (3 : ℝ) ^ (-(4 : ℝ) * alphaParam t)) *
          ENNReal.ofReal Cfrac *
          ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2)) *
          ENNReal.rpow E (1 / 2) := mul_le_mul_right hroot _
    _ = _ := by ac_rfl

end

end CoarseDeGiorgi.Harnack.Log
