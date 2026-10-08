import CoarseDeGiorgi.Harnack.Log.Centering
import CoarseDeGiorgi.Harnack.Log.LocalOscillation
import CoarseDeGiorgi.Harnack.Log.ContrastFinite
import CoarseDeGiorgi.Harnack.Log.Membership
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.WeightedEnergy

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The local fractional oscillation bound and fixed-grid paths give a
parameter-only global center estimate. Its average-center counterpart follows
from the finite-measure Holder lemma. -/
theorem log_global_center_of_energy_bound {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (C_E : ℝ≥0∞) (hCE : C_E < ⊤) :
    ∃ C₂ : ℝ≥0∞, C₂ < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
        (_hrange : spatialMomentRange a ha p q s t)
        (u : Vec d → ℝ) (G : Vec d → Vec d)
        (_hu : IsWeightedSupersolution a (originCube 1) u G)
        (_hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
        (ε : ℝ) (_hε : 0 < ε),
        weightedEnergy a (originCube (15 / 16 : ℝ))
          (fun x => (u x + ε)⁻¹ • G x) ≤
          C_E * upperMoment a ha s p hs (le_of_lt hp) →
        ∃ c : ℝ,
          eLpNorm (fun x => Real.log (u x + ε) - c)
            (ENNReal.ofReal (paramR q)) (volume.restrict (originCube (7 / 8 : ℝ))) ≤
            C₂ * (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow (1 / 2) ∧
          eLpNorm (fun _ : Vec d => c - volumeAverage (originCube (7 / 8 : ℝ))
            (fun x => Real.log (u x + ε)))
            (ENNReal.ofReal (paramR q)) (volume.restrict (originCube (7 / 8 : ℝ))) ≤
            C₂ * (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow (1 / 2) := by
  obtain ⟨Cmean, Cfrac, hCmean, hCfrac, hLocalAll⟩ :=
    log_local_oscillation_of_energy_bound hd p q s t hp hq hs ht hθ
  let A := ENNReal.ofReal (Cmean * (3 : ℝ) ^ (-(4 : ℝ) * alphaParam t)) *
    ENNReal.ofReal Cfrac
  let baseFactor := A * ENNReal.rpow C_E (1 / 2)
  have hATop : A < ⊤ := by
    dsimp [A]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hbaseFactorTop : baseFactor < ⊤ := by
    dsimp [baseFactor]
    exact ENNReal.mul_lt_top hATop
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCE.ne)
  have : NeZero d := ⟨by omega⟩
  let S := originCube (d := d) (7 / 8 : ℝ)
  let K := fixedLogGrid_pathConstant (d := d) (paramR q)
  have hK : 0 ≤ K := fixedLogGrid_pathConstant_nonneg (paramR q)
  let gridCoeff : ℝ := (fixedLogGrid (d := d)).card +
    (35 * (d : ℝ)) * K * (volume S).toReal ^ (1 / paramR q)
  have hgridCoeff : 0 ≤ gridCoeff := by
    dsimp [gridCoeff]
    positivity
  let C₂ := ENNReal.ofReal gridCoeff * baseFactor
  have hC₂ : C₂ < ⊤ := by
    dsimp [C₂]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hbaseFactorTop
  refine ⟨C₂, hC₂, ?_⟩
  intro a ha hrange u G hu hnonneg ε hε henergy
  have hcontrastTop :
      contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq) < ⊤ :=
    contrast_lt_top_of_spatialMomentRange a ha p q s t hp hq hs ht hrange
  have hUpper : upperMoment a ha s p hs (le_of_lt hp) < ⊤ := by
    rcases hrange with
      ⟨_hp1, _hq1, _hs0, _ht0, _hp', _hq', _hs', _ht', _hθ', hUpper, _hLower⟩
    exact hUpper
  have hLower : 0 < lowerMoment a ha t q ht (le_of_lt hq) := by
    rcases hrange with
      ⟨_hp1, _hq1, _hs0, _ht0, _hp', _hq', _hs', _ht', _hθ', _hUpper, hLower⟩
    exact hLower
  have hMem := log_memH1a hd a ha hu hnonneg ε hε
  let w : Vec d → ℝ := fun x => Real.log (u x + ε)
  let Glog : Vec d → Vec d := fun x => (u x + ε)⁻¹ • G x
  let E := C_E * upperMoment a ha s p hs (le_of_lt hp)
  have hlocalOsc := hLocalAll a ha hrange w Glog hMem E (by simpa [E, Glog] using henergy)
  let L := lowerMoment a ha t q ht (le_of_lt hq)
  let U := upperMoment a ha s p hs (le_of_lt hp)
  let localBound := A * ENNReal.rpow L (-1 / 2) * ENNReal.rpow E (1 / 2)
  let contrastValue := contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)
  let contrastHalf := ENNReal.rpow contrastValue (1 / 2)
  have hLowerFactorTop : ENNReal.rpow L (-1 / 2) < ⊤ := by
    by_cases hLtop : L = ⊤
    · rw [hLtop]
      simp [ENNReal.top_rpow_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]
    · exact lt_top_iff_ne_top.mpr <| ENNReal.rpow_ne_top_of_ne_zero hLower.ne' hLtop
  have hETop : E < ⊤ := by
    dsimp [E, U]
    exact ENNReal.mul_lt_top hCE hUpper
  have hERootTop : ENNReal.rpow E (1 / 2) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hETop.ne
  have hlocalBoundTop : localBound < ⊤ := by
    dsimp [localBound]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hATop hLowerFactorTop) hERootTop
  have hcontrastHalfTop : contrastHalf < ⊤ := by
    dsimp [contrastHalf]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hcontrastTop.ne
  have hdivRpow : contrastHalf = ENNReal.rpow U (1 / 2) /
      ENNReal.rpow L (1 / 2) := by
    change ENNReal.rpow (U / L) (1 / 2) = _
    exact ENNReal.div_rpow_of_nonneg U L (by norm_num)
  have hnegativeRpow : ENNReal.rpow L (-1 / 2) =
      (ENNReal.rpow L (1 / 2))⁻¹ := by
    calc
      _ = L ^ (-1 / 2 : ℝ) := rfl
      _ = (L ^ (1 / 2 : ℝ))⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, ENNReal.rpow_neg]
      _ = _ := rfl
  have hpair : L ^ (-1 / 2 : ℝ) * U ^ (1 / 2 : ℝ) =
      contrastHalf := by
    change ENNReal.rpow L (-1 / 2) * ENNReal.rpow U (1 / 2) = contrastHalf
    calc
      _ = (ENNReal.rpow L (1 / 2))⁻¹ * ENNReal.rpow U (1 / 2) := by
        rw [hnegativeRpow]
      _ = ENNReal.rpow U (1 / 2) / ENNReal.rpow L (1 / 2) := by
        rw [div_eq_mul_inv]
        ac_rfl
      _ = contrastHalf := hdivRpow.symm
  have henergyRootProduct : E ^ (1 / 2 : ℝ) =
      C_E ^ (1 / 2 : ℝ) * U ^ (1 / 2 : ℝ) := by
    dsimp [E, U]
    exact ENNReal.mul_rpow_of_ne_top hCE.ne hUpper.ne (1 / 2)
  have hlocalFactor : localBound = baseFactor * contrastHalf := by
    dsimp [localBound, baseFactor]
    rw [henergyRootProduct]
    calc
      _ = (A * C_E ^ (1 / 2 : ℝ)) * (L ^ (-1 / 2 : ℝ) * U ^ (1 / 2 : ℝ)) := by
        ac_rfl
      _ = (A * C_E ^ (1 / 2 : ℝ)) * contrastHalf := by rw [hpair]
      _ = _ := rfl
  have hlocalBound : ∀ z ∈ fixedLogGrid (d := d),
      eLpNorm (fun x => w x - volumeAverage (auxCube 4 z) w)
        (ENNReal.ofReal (paramR q)) (volume.restrict (auxCube 4 z)) ≤ localBound := by
    intro z hz
    calc
      _ ≤ A * ENNReal.rpow L (-1 / 2) * ENNReal.rpow E (1 / 2) := by
        simpa [w, A, L] using hlocalOsc z hz
      _ = localBound := rfl
  let B := localBound.toReal
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hBof : ENNReal.ofReal B = localBound := ENNReal.ofReal_toReal hlocalBoundTop.ne
  have : NeZero d := ⟨by omega⟩
  have hSfacts := originCube_sevenEighths_volume_facts (d := d)
  have hvol : 0 < volume (originCube (d := d) (7 / 8 : ℝ)) := hSfacts.1
  let S := originCube (d := d) (7 / 8 : ℝ)
  let μ := volume.restrict S
  let : IsFiniteMeasure μ := hSfacts.2
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
    intro hz
    have hzero : volume S = 0 := by
      have h := congrArg (fun ν : Measure (Vec d) => ν Set.univ) hz
      simpa [hmass] using h
    exact hvol.ne' hzero
  have hvoltop : volume S ≠ ⊤ := by
    intro hz
    have htop : μ Set.univ = ⊤ := by rw [hmass, hz]
    exact (measure_ne_top μ Set.univ) htop
  have hvolReal : 0 < (volume S).toReal := ENNReal.toReal_pos hvol.ne' hvoltop
  have hrparam : 1 < paramR q := by
    dsimp [paramR]
    rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  have hrpos : 0 < paramR q := lt_trans zero_lt_one hrparam
  have hp0 : ENNReal.ofReal (paramR q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hrpos).ne'
  have hvolPow : 0 ≤ (volume S).toReal ^ (1 / paramR q) :=
    Real.rpow_nonneg hvolReal.le _
  have hwUnit : AEStronglyMeasurable w (volume.restrict (originCube (d := d) 1)) := by
    simpa [w] using hMem.1
  have hcenterRaw := log_global_center_from_local_bounds (r := paramR q) B
      hrparam hB w hwUnit (by
        intro z hz
        calc
          _ ≤ localBound := hlocalBound z hz
          _ = ENNReal.ofReal B := hBof.symm)
  let D := (35 * (d : ℝ)) * (K * B)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hconstNorm : eLpNorm (fun _ : Vec d => D) (ENNReal.ofReal (paramR q)) μ =
      ENNReal.ofReal (D * (volume S).toReal ^ (1 / paramR q)) := by
    rw [eLpNorm_const D hp0 hμ0, Real.enorm_eq_ofReal_abs, hmass,
      ENNReal.toReal_ofReal hrpos.le]
    conv_lhs =>
      rw [← ENNReal.ofReal_toReal hvoltop,
        ENNReal.ofReal_rpow_of_nonneg hvolReal.le (by positivity),
        ← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [abs_of_nonneg hD]
  have hgridTerms :
      ENNReal.ofReal ((fixedLogGrid (d := d)).card : ℝ) * ENNReal.ofReal B +
          ENNReal.ofReal (D * (volume S).toReal ^ (1 / paramR q)) =
        ENNReal.ofReal (gridCoeff * B) := by
    let coeff : ℝ := (35 * (d : ℝ)) * K * (volume S).toReal ^ (1 / paramR q)
    have hDmul : D * (volume S).toReal ^ (1 / paramR q) = coeff * B := by
      dsimp [D]
      ring
    have hcard : 0 ≤ ((fixedLogGrid (d := d)).card : ℝ) := by positivity
    have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
    calc
      _ = ENNReal.ofReal (((fixedLogGrid (d := d)).card : ℝ) * B) +
          ENNReal.ofReal (coeff * B) := by
            congr 1
            · exact (ENNReal.ofReal_mul hcard).symm
            · exact congrArg ENNReal.ofReal hDmul
      _ = ENNReal.ofReal
          ((((fixedLogGrid (d := d)).card : ℝ) * B) + coeff * B) :=
            (ENNReal.ofReal_add (mul_nonneg hcard hB) (mul_nonneg hcoeff hB)).symm
      _ = ENNReal.ofReal (gridCoeff * B) := by
            congr 1
            dsimp [gridCoeff, coeff]
            ring
  let zeroGrid : Fin d → ℤ := fun _ => 0
  let c := volumeAverage (auxCube 4 zeroGrid) w
  have hglobal : eLpNorm (fun x => w x - c) (ENNReal.ofReal (paramR q)) μ ≤
      ENNReal.ofReal (gridCoeff * B) := by
    calc
      _ ≤ ENNReal.ofReal (fixedLogGrid (d := d)).card * ENNReal.ofReal B +
          eLpNorm (fun _ : Vec d => D) (ENNReal.ofReal (paramR q)) μ := by
            simpa [S, μ, c, zeroGrid, D, K] using hcenterRaw
      _ = ENNReal.ofReal (gridCoeff * B) := by rw [hconstNorm]; exact hgridTerms
  have hcenterCoeff : ENNReal.ofReal (gridCoeff * B) = C₂ * contrastHalf := by
    calc
      _ = ENNReal.ofReal gridCoeff * ENNReal.ofReal B :=
        ENNReal.ofReal_mul hgridCoeff
      _ = ENNReal.ofReal gridCoeff * localBound := by rw [hBof]
      _ = C₂ * contrastHalf := by
        rw [hlocalFactor]
        dsimp [C₂]
        ac_rfl
  have hglobal' : eLpNorm (fun x => w x - c) (ENNReal.ofReal (paramR q)) μ ≤
      C₂ * contrastHalf := hglobal.trans_eq hcenterCoeff
  have hcenterTop : C₂ * contrastHalf < ⊤ := ENNReal.mul_lt_top hC₂ hcontrastHalfTop
  have hglobalReal : eLpNorm (fun x => w x - c)
      (ENNReal.ofReal (paramR q)) μ ≤ ENNReal.ofReal (C₂ * contrastHalf).toReal := by
    calc
      _ ≤ C₂ * contrastHalf := hglobal'
      _ = ENNReal.ofReal (C₂ * contrastHalf).toReal :=
        (ENNReal.ofReal_toReal hcenterTop.ne).symm
  have haverage := log_average_center_bound_of_global (paramR q)
    (C₂ * contrastHalf).toReal c hrparam ENNReal.toReal_nonneg w
    hglobalReal hvol
  have haverage' : eLpNorm (fun _ : Vec d => c - volumeAverage S w)
      (ENNReal.ofReal (paramR q)) μ ≤ C₂ * contrastHalf := by
    simpa only [ENNReal.ofReal_toReal hcenterTop.ne] using haverage
  refine ⟨c, ?_, ?_⟩
  · simpa [w, S, μ, contrastHalf, contrastValue] using hglobal'
  · simpa [w, S, μ, contrastHalf, contrastValue] using haverage'

end

end CoarseDeGiorgi.Harnack.Log
