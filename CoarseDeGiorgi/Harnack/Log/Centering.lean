module

public import CoarseDeGiorgi.Harnack.Log.GlobalOscillation
public import CoarseDeGiorgi.Harnack.Log.OverlapPaths
public import CoarseDeGiorgi.LowerFractional.MeanCube
public import CoarseDeGiorgi.LowerFractional.CubeDomain

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The fixed `7/8` Harnack cube has positive, finite volume in every
nonzero dimension. -/
theorem originCube_sevenEighths_volume_facts {d : ℕ} [NeZero d] :
    0 < volume (originCube (d := d) (7 / 8 : ℝ)) ∧
      IsFiniteMeasure (volume.restrict (originCube (d := d) (7 / 8 : ℝ))) := by
  let S := originCube (d := d) (7 / 8 : ℝ)
  let U := originCube (d := d) 1
  have hScube : IsOpen S := by
    change IsOpen {x : Vec d | ∀ i, (-(7 / 8 / 2 : ℝ)) < x i ∧ x i < 7 / 8 / 2}
    simp only [← Set.iInter_ofPred]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_Ioo.preimage (continuous_apply i)
  have hSmeas : MeasurableSet S := hScube.measurableSet
  have hSne : S.Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    intro i
    constructor <;> norm_num
  have hSpos : 0 < volume S := IsOpen.measure_pos volume hScube hSne
  let zero : Fin d → ℤ := fun _ => 0
  have hUeq : U = auxCube 1 zero := by
    ext x
    simp [U, zero, originCube, auxCube, sub_self, sub_zero,
      Int.cast_zero, zero_mul, abs_lt]
  have hUdomain : IsOpenBoundedConvexDomain U := by
    rw [hUeq]
    exact LowerFractional.auxCube_isOpenBoundedConvexDomain 1 zero
  let : IsFiniteMeasure (volume.restrict U) := hUdomain.isFiniteMeasure_restrict_volume
  have hUmeas : MeasurableSet U := hUdomain.isOpen.measurableSet
  have hUtop : volume U ≠ ⊤ := by
    have h := measure_ne_top (volume.restrict U) Set.univ
    simpa [Measure.restrict_apply, hUmeas] using h
  have hSsub : S ⊆ U := by
    intro x hx i
    have hxi := hx i
    change -(7 / 8 / 2 : ℝ) < x i ∧ x i < 7 / 8 / 2 at hxi
    change -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2
    constructor <;> norm_num <;> linarith
  have hStop : volume S < ⊤ := measure_lt_top_of_subset hSsub hUtop
  refine ⟨hSpos, ?_⟩
  refine ⟨?_⟩
  simpa [Measure.restrict_apply, hSmeas] using hStop

/-- Convert uniform cube oscillation bounds into a global oscillation bound
about the zero-grid auxiliary mean. The neighboring-center estimate uses
finite-overlap Holder, and the path length is bounded by the fixed grid's
coordinate radius. -/
theorem log_global_center_from_local_bounds {d : ℕ} (r B : ℝ)
    (hr : 1 < r) (hB : 0 ≤ B) (w : Vec d → ℝ)
    (hw : AEStronglyMeasurable w (volume.restrict (originCube (d := d) 1)))
    (hLocal : ∀ z ∈ fixedLogGrid,
      eLpNorm (fun x => w x - volumeAverage (auxCube 4 z) w)
        (ENNReal.ofReal r) (volume.restrict (auxCube 4 z)) ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => w x - volumeAverage (auxCube 4 (fun _ : Fin d => 0)) w)
      (ENNReal.ofReal r) (volume.restrict (originCube (7 / 8 : ℝ))) ≤
      ENNReal.ofReal (fixedLogGrid (d := d)).card * ENNReal.ofReal B +
        eLpNorm (fun _ : Vec d =>
          (35 * (d : ℝ)) * (fixedLogGrid_pathConstant (d := d) r * B))
          (ENNReal.ofReal r) (volume.restrict (originCube (7 / 8 : ℝ))) := by
  let K := fixedLogGrid_pathConstant (d := d) r
  have hK : 0 ≤ K := fixedLogGrid_pathConstant_nonneg (d := d) r
  have hstep := fixedLogGrid_neighbor_steps_of_local_bounds r B hr hB w hLocal
  let z₀ : Fin d → ℤ := fun _ => 0
  let D : ℝ := (35 * (d : ℝ)) * (K * B)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCenters : ∀ z ∈ fixedLogGrid,
      |logGridMean w z - logGridMean w z₀| ≤ D := by
    intro z hz
    have hpath := fixedLogGrid_all_mean_bounds
      (fun y => volumeAverage (auxCube 4 y) w) (K * B)
      (mul_nonneg hK hB) hstep z hz
    simpa [D, z₀, logGridMean] using hpath
  have hglobal := log_global_oscillation_of_grid_bounds r hr.le w hw z₀ B D hD
    hLocal hCenters
  simpa [K, z₀, logGridMean, logOscillationDomain] using hglobal

/-- On the finite-volume Harnack cube, a global `Lʳ` bound controls the
constant difference between a chosen center and the domain average. -/
theorem log_average_center_bound_of_global {d : ℕ}
    [IsFiniteMeasure (volume.restrict (originCube (d := d) (7 / 8 : ℝ)))]
    (r B c : ℝ) (hr : 1 < r) (hB : 0 ≤ B)
    (w : Vec d → ℝ) (hcenter :
      eLpNorm (fun x => w x - c) (ENNReal.ofReal r)
        (volume.restrict (originCube (7 / 8 : ℝ))) ≤ ENNReal.ofReal B)
    (hvol : 0 < volume (originCube (d := d) (7 / 8 : ℝ))) :
    eLpNorm (fun _ : Vec d => c -
        volumeAverage (originCube (7 / 8 : ℝ)) w)
      (ENNReal.ofReal r) (volume.restrict (originCube (7 / 8 : ℝ))) ≤ ENNReal.ofReal B := by
  let S := originCube (d := d) (7 / 8 : ℝ)
  let μ := volume.restrict S
  let f : Vec d → ℝ := fun x => w x - c
  have hSmeas : MeasurableSet S := by
    have hopen : IsOpen S := by
      change IsOpen {x : Vec d | ∀ i, (-(7 / 8 / 2 : ℝ)) < x i ∧ x i < 7 / 8 / 2}
      simp only [← Set.iInter_ofPred]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_Ioo.preimage (continuous_apply i)
    exact hopen.measurableSet
  have hmass : μ Set.univ = volume S := by
    simp [μ, Measure.restrict_apply]
  have hμ0 : μ ≠ 0 := by
    intro hzero
    have hzero' : volume S = 0 := by
      have h := congrArg (fun ν : Measure (Vec d) => ν Set.univ) hzero
      simpa [hmass] using h
    exact hvol.ne' hzero'
  have hvoltop : volume S ≠ ⊤ := by
    intro htop
    have hmassTop : μ Set.univ = ⊤ := by rw [hmass, htop]
    exact (measure_ne_top μ Set.univ) hmassTop
  have hV : 0 < (volume S).toReal := ENNReal.toReal_pos hvol.ne' hvoltop
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  obtain ⟨hIntegrable, hIntegral⟩ :=
    CoarseDeGiorgi.Harnack.LogLimit.integral_abs_le_of_eLpNorm_le hr hB hcenter
  have hfOn : IntegrableOn f S := by
    change Integrable f μ
    exact hIntegrable
  have hcOn : IntegrableOn (fun _ : Vec d => c) S := integrable_const _
  have hwOn : IntegrableOn w S := by
    have hsum : IntegrableOn (fun x => (w x - c) + c) S := hfOn.add hcOn
    convert hsum using 1
    funext x
    ring
  have havg : volumeAverage S f = volumeAverage S w - c := by
    have hsub := volumeAverage_sub hwOn hcOn
    rw [show f = w - (fun _ : Vec d => c) by
      funext x
      simp [f], hsub, volumeAverage_const (ne_of_gt hV)]
  have hIntegralAbs : ∫ x in S, |f x| ≤
      B * (volume S).toReal ^ (1 - 1 / r) := by
    simpa [μ, f, hmass, Real.norm_eq_abs] using hIntegral
  have hnormInt : |∫ x in S, f x| ≤ ∫ x in S, |f x| := by
    have h := norm_integral_le_integral_norm (μ := μ) f
    simpa [μ, f, Real.norm_eq_abs] using h
  let δ := c - volumeAverage S w
  have hδ : δ = -volumeAverage S f := by
    dsimp [δ]
    rw [havg]
    ring
  have hδbound : |δ| ≤ B * (volume S).toReal ^ (1 - 1 / r) /
      (volume S).toReal := by
    rw [hδ, abs_neg]
    unfold volumeAverage
    rw [abs_mul, abs_of_pos (inv_pos.mpr hV)]
    calc
      (volume S).toReal⁻¹ * |∫ x in S, f x| ≤
          (volume S).toReal⁻¹ * ∫ x in S, |f x| :=
            mul_le_mul_of_nonneg_left hnormInt (inv_nonneg.mpr hV.le)
      _ ≤ (volume S).toReal⁻¹ *
          (B * (volume S).toReal ^ (1 - 1 / r)) :=
            mul_le_mul_of_nonneg_left hIntegralAbs (inv_nonneg.mpr hV.le)
      _ = B * (volume S).toReal ^ (1 - 1 / r) /
          (volume S).toReal := by ring
  have hprod : |δ| * (volume S).toReal ^ (1 / r) ≤ B := by
    have hpow : (volume S).toReal ^ (1 - 1 / r) /
        (volume S).toReal * (volume S).toReal ^ (1 / r) = 1 := by
      calc
        _ = (volume S).toReal ^ (1 - 1 / r) *
            (volume S).toReal ^ (1 / r) / (volume S).toReal := by ring
        _ = (volume S).toReal ^ ((1 - 1 / r) + (1 / r)) /
            (volume S).toReal := by
              rw [← Real.rpow_add hV]
        _ = 1 := by
          rw [show (1 - 1 / r) + (1 / r) = 1 by ring, Real.rpow_one]
          field_simp
    calc
      |δ| * (volume S).toReal ^ (1 / r) ≤
          (B * (volume S).toReal ^ (1 - 1 / r) /
            (volume S).toReal) * (volume S).toReal ^ (1 / r) :=
              mul_le_mul_of_nonneg_right hδbound
                (Real.rpow_nonneg hV.le _)
      _ = B := by
        calc
          _ = B * ((volume S).toReal ^ (1 - 1 / r) /
              (volume S).toReal * (volume S).toReal ^ (1 / r)) := by ring
          _ = B := by rw [hpow]; ring
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hrpos).ne'
  have hconst : eLpNorm (fun _ : Vec d => δ) (ENNReal.ofReal r) μ =
      ENNReal.ofReal (|δ| * (volume S).toReal ^ (1 / r)) := by
    rw [eLpNorm_const δ hp0 hμ0, Real.enorm_eq_ofReal_abs, hmass,
      ENNReal.toReal_ofReal hrpos.le]
    conv_lhs =>
      rw [← ENNReal.ofReal_toReal hvoltop,
        ENNReal.ofReal_rpow_of_nonneg hV.le (by positivity),
        ← ENNReal.ofReal_mul (abs_nonneg _)]
  simpa [S, μ, δ, hconst] using (ENNReal.ofReal_le_ofReal hprod)

end

end CoarseDeGiorgi.Harnack.Log
