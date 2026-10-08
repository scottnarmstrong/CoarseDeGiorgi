module

public import CoarseDeGiorgi.Harnack.Iterations.NormalizedMomentOrder
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace CoarseDeGiorgi.Harnack.ReverseMoments

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- Volume of the centered open cube in the project's radius convention. -/
theorem originCube_volume {d : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    volume (CoarseDeGiorgi.originCube (d := d) R) = ENNReal.ofReal (R ^ d) := by
  have hset : CoarseDeGiorgi.originCube (d := d) R =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(R / 2)) (R / 2)) := by
    ext x
    simp [CoarseDeGiorgi.originCube, Set.mem_pi, Set.mem_Ioo]
  rw [hset, Real.volume_pi_Ioo]
  simp only [Finset.prod_const, Finset.card_fin]
  rw [show R / 2 - -(R / 2) = R by ring, ← ENNReal.ofReal_pow hR d]

/-- The volume correction from passing between the two normalized cube moments
is uniformly at most `2^d` on the radii used in Phase 5. -/
theorem originCube_normalization_factor_le {d : ℕ} {ρ R χ : ℝ}
    (hρ : 1 / 2 ≤ ρ) (hRpos : 0 < R) (hR : R ≤ 1) (hχ : 1 ≤ χ) :
    (volume.restrict (CoarseDeGiorgi.originCube (d := d) ρ) Set.univ) ^ (-1 / χ) *
        (volume.restrict (CoarseDeGiorgi.originCube (d := d) R) Set.univ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d) := by
  have hρpos : 0 < ρ := by linarith
  have hχpos : 0 < χ := lt_of_lt_of_le zero_lt_one hχ
  have hρcube : 0 < ρ ^ d := by positivity
  simp only [Measure.restrict_apply_univ]
  rw [originCube_volume ρ hρpos.le, originCube_volume R hRpos.le,
    ENNReal.ofReal_rpow_of_pos hρcube]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg hρpos.le d) _)]
  apply ENNReal.ofReal_le_ofReal
  have hρpow : (1 / 2 : ℝ) ^ d ≤ ρ ^ d := by gcongr
  have hexp : -1 / χ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hχpos.le
  have hApos : 0 < (1 / 2 : ℝ) ^ d := by positivity
  have hAle : (1 / 2 : ℝ) ^ d ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hχinv : 1 / χ ≤ 1 := (div_le_iff₀ hχpos).2 (by nlinarith [hχ])
  have hExpOrder : (-1 : ℝ) ≤ -1 / χ := by rw [neg_div]; linarith
  have hAinvExp : ((1 / 2 : ℝ) ^ d) ^ (-1 / χ) ≤
      ((1 / 2 : ℝ) ^ d) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hApos hAle hExpOrder
  have hAinv : ((1 / 2 : ℝ) ^ d) ^ (-1 : ℝ) = (2 : ℝ) ^ d := by
    rw [Real.rpow_neg_one]
    norm_num [one_div_pow]
  have hRpow : R ^ d ≤ 1 := pow_le_one₀ (by positivity) hR
  calc
    _ ≤ ((1 / 2 : ℝ) ^ d) ^ (-1 / χ) * 1 := by
      exact mul_le_mul
        (Real.rpow_le_rpow_of_nonpos hApos hρpow hexp) hRpow
        (by positivity) (by positivity)
    _ ≤ (2 : ℝ) ^ d := by simpa using hAinvExp.trans_eq hAinv

/-- Raise a normalized moment to any positive power while retaining its
volume factor explicitly. -/
theorem normalizedLpMoment_rpow_eq_eLpNorm_rpow {d : ℕ}
    (V : Set (Vec d)) (f : Vec d → ℝ) {b r : ℝ}
    (hb : 0 < b) (hr : 0 < r)
    (hf : AEStronglyMeasurable f (volume.restrict V))
    (hV0 : volume.restrict V Set.univ ≠ 0)
    (hVtop : volume.restrict V Set.univ ≠ ⊤) :
    CoarseDeGiorgi.normalizedLpMoment b hb V f ^ r =
      (volume.restrict V Set.univ) ^ (-r / b) *
        (eLpNorm f (ENNReal.ofReal b) (volume.restrict V)) ^ r := by
  let μ : ℝ≥0∞ := volume.restrict V Set.univ
  have hμ0 : μ ≠ 0 := by simpa [μ] using hV0
  have hμtop : μ ≠ ⊤ := by simpa [μ] using hVtop
  have hnormeq : CoarseDeGiorgi.normalizedLpMoment b hb V f =
      μ ^ (-1 / b) * eLpNorm f (ENNReal.ofReal b) (volume.restrict V) := by
    rw [CoarseDeGiorgi.Harnack.Iterations.normalizedLpMoment_eq_eLpNorm' V f hb]
    have h := eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hb).ne'
      ENNReal.ofReal_ne_top hf
    rw [ENNReal.toReal_ofReal hb.le] at h
    calc
      _ = μ ^ (-1 / b) * eLpNorm' f b (volume.restrict V) := by
        simp only [μ]
      _ = _ := congrArg (fun n => μ ^ (-1 / b) * n) h.symm
  rw [hnormeq, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  have hexp : (-1 / b : ℝ) * r = -r / b := by ring
  rw [← hexp]
  exact congrArg (fun x => x *
    (eLpNorm f (ENNReal.ofReal b) (volume.restrict V)) ^ r)
    (ENNReal.rpow_mul μ (-1 / b) r).symm

/-- Convert an unnormalized reverse norm inequality into the corresponding
normalized moment inequality, isolating the volume-ratio loss. -/
theorem normalizedLpMoment_reverse_of_eLpNorm {d : ℕ}
    (V W : Set (Vec d)) (f : Vec d → ℝ) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q)
    (hfV : AEStronglyMeasurable f (volume.restrict V))
    (hfW : AEStronglyMeasurable f (volume.restrict W))
    (hV0 : volume.restrict V Set.univ ≠ 0)
    (hVtop : volume.restrict V Set.univ ≠ ⊤)
    (hW0 : volume.restrict W Set.univ ≠ 0)
    (hWtop : volume.restrict W Set.univ ≠ ⊤)
    (K A : ℝ≥0∞)
    (hvolume : (volume.restrict V Set.univ) ^ (-q / p) *
        (volume.restrict W Set.univ) ≤ K)
    (hnorm : eLpNorm f (ENNReal.ofReal p) (volume.restrict V) ≤
      A * eLpNorm f (ENNReal.ofReal q) (volume.restrict W)) :
    CoarseDeGiorgi.normalizedLpMoment p hp V f ^ q ≤
      K * A ^ q *
        CoarseDeGiorgi.normalizedLpMoment q hq W f ^ q := by
  have hmomentV := normalizedLpMoment_rpow_eq_eLpNorm_rpow V f hp hq hfV hV0 hVtop
  have hmomentW := normalizedLpMoment_rpow_eq_eLpNorm_rpow W f hq hq hfW hW0 hWtop
  have hnormPow := ENNReal.rpow_le_rpow hnorm hq.le
  have houterNorm :
      eLpNorm f (ENNReal.ofReal q) (volume.restrict W) ^ q =
        (volume.restrict W Set.univ) *
          CoarseDeGiorgi.normalizedLpMoment q hq W f ^ q := by
    have hmomentW' : CoarseDeGiorgi.normalizedLpMoment q hq W f ^ q =
        (volume.restrict W Set.univ)⁻¹ *
          (eLpNorm f (ENNReal.ofReal q) (volume.restrict W)) ^ q := by
      rw [hmomentW]
      have hexp : (-q / q : ℝ) = -1 := by field_simp
      rw [hexp, ENNReal.rpow_neg_one]
    calc
      _ = ((volume.restrict W Set.univ) *
            (volume.restrict W Set.univ)⁻¹) *
            (eLpNorm f (ENNReal.ofReal q) (volume.restrict W)) ^ q := by
              rw [ENNReal.mul_inv_cancel hW0 hWtop, one_mul]
      _ = _ := by rw [hmomentW']; ac_rfl
  rw [hmomentV]
  calc
    _ ≤ (volume.restrict V Set.univ) ^ (-q / p) *
        (A * eLpNorm f (ENNReal.ofReal q) (volume.restrict W)) ^ q :=
      mul_le_mul_of_nonneg_left hnormPow (by positivity)
    _ = (volume.restrict V Set.univ) ^ (-q / p) * A ^ q *
        (eLpNorm f (ENNReal.ofReal q) (volume.restrict W)) ^ q := by
      rw [ENNReal.mul_rpow_of_nonneg A _ hq.le]
      ac_rfl
    _ = ((volume.restrict V Set.univ) ^ (-q / p) *
          (volume.restrict W Set.univ)) * A ^ q *
          CoarseDeGiorgi.normalizedLpMoment q hq W f ^ q := by
      rw [houterNorm]
      ac_rfl
    _ ≤ K * A ^ q *
        CoarseDeGiorgi.normalizedLpMoment q hq W f ^ q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hvolume (by positivity)) (by positivity)

end

end CoarseDeGiorgi.Harnack.ReverseMoments
