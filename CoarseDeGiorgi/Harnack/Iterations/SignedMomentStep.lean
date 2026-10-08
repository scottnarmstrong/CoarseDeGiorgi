import CoarseDeGiorgi.Harnack.Iterations.MomentPower
import CoarseDeGiorgi.Harnack.ReverseMoments.NormalizedReverse
import CoarseDeGiorgi.Assembly.HybridParameters
import Mathlib.Tactic

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

private theorem iteration_paramR_pos {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) : 0 < paramR q :=
  ReverseMoments.paramR_pos_of_harnack_facts hd hp hq hs ht hθ

private theorem iteration_rStar_pos {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) : 0 < rStarParam (d := d) q t :=
  ReverseMoments.rStarParam_pos_of_harnack_facts hd hp hq hs ht hθ

private theorem measurable_originCube {d : ℕ} (R : ℝ) :
    MeasurableSet (originCube (d := d) R) := by
  have hopen : IsOpen (originCube (d := d) R) := by
    change IsOpen {x : Vec d | ∀ i, x i ∈ Set.Ioo (-(R / 2)) (R / 2)}
    simp only [← Set.iInter_ofPred]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_Ioo.preimage (continuous_apply i)
  exact hopen.measurableSet

/-- The normalized reverse estimate becomes the source signed-moment step
after substituting `m = z / r` and identifying the scaled normalized moments.
-/
theorem signed_moment_step_of_normalized_reverse {d : ℕ}
    (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (C : ℝ≥0∞) (_hC1 : 1 ≤ C) (_hCtop : C < ⊤)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (_hrange : spatialMomentRange a ha p q s t)
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hnonneg : ∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x)
    (_hsup : IsWeightedSupersolution a (originCube 1) u G)
    (ε : ℝ) (hε : 0 < ε)
    (hReverse :
      ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
        ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let v : Vec d → ℝ := fun x => (u x + ε) ^ m
          (CoarseDeGiorgi.normalizedLpMoment
              (rStarParam (d := d) q t)
              (iteration_rStar_pos hd hp hq hs ht hθ)
              (originCube ρ) v) ^ (paramR q) ≤
            C * (ENNReal.ofReal (((R - ρ) / 2) ^
                (-(gammaOneParam (d := d) q t +
                  gammaTwoParam (d := d) p q t * alphaParam t /
                    paramTheta d p q s t)))) ^ (paramR q) *
              (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                contrast a ha s t p q hs ht hp.le hq.le).rpow
                  (alphaParam t * paramR q /
                    (2 * paramTheta d p q s t)) *
              (CoarseDeGiorgi.normalizedLpMoment (paramR q)
          (iteration_paramR_pos hd hp hq hs ht hθ)
                (originCube R) v) ^ (paramR q))
    (z : ℝ) (hz : z ≠ 0) (hzr : z < paramR q / 2)
    (ρ R : ℝ) (hρ : 1 / 2 ≤ ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    let r := paramR q
    let rStar := rStarParam (d := d) q t
    let χ := rStar / r
    let W : Vec d → ℝ := fun x =>
      if 0 < z then u x + ε else (u x + ε)⁻¹
    CoarseDeGiorgi.normalizedLpMoment (χ * |z|)
      (mul_pos (div_pos (iteration_rStar_pos hd hp hq hs ht hθ)
        (iteration_paramR_pos hd hp hq hs ht hθ)) (abs_pos.mpr hz))
      (originCube ρ) W ^ |z| ≤
      C * (ENNReal.ofReal (((R - ρ) / 2) ^
          (-(gammaOneParam (d := d) q t +
            gammaTwoParam (d := d) p q t * alphaParam t /
              paramTheta d p q s t)))) ^ r *
        (1 + ENNReal.ofReal (powerFactor (z / r) ^ 2) *
          contrast a ha s t p q hs ht hp.le hq.le).rpow
            (alphaParam t * r / (2 * paramTheta d p q s t)) *
        CoarseDeGiorgi.normalizedLpMoment |z|
          (abs_pos.mpr hz) (originCube R) W ^ |z| := by
  obtain ⟨_, _, hr1, _, _, _, _, hrStar⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  let r : ℝ := paramR q
  let rStar : ℝ := rStarParam (d := d) q t
  let χ : ℝ := rStar / r
  let W : Vec d → ℝ := fun x =>
      if 0 < z then u x + ε else (u x + ε)⁻¹
  let rPos : 0 < r := iteration_paramR_pos hd hp hq hs ht hθ
  let rStarPos : 0 < rStar := iteration_rStar_pos hd hp hq hs ht hθ
  have hχ : 1 < χ := by
    dsimp [χ, r, rStar]
    exact (lt_div_iff₀ (iteration_paramR_pos hd hp hq hs ht hθ)).2
      (by simpa using hrStar)
  let sm : ℝ := |z| / r
  have hsm : 0 < sm := by dsimp [sm]; exact div_pos (abs_pos.mpr hz) rPos
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hρ
  have hRpos : 0 < R := lt_trans hρpos hρR
  have hUposOne : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)),
      0 < u x + ε := by
    filter_upwards [hnonneg] with x hx
    exact add_pos_of_nonneg_of_pos hx hε
  have hUposR : ∀ᵐ x ∂(volume.restrict (originCube (d := d) R)),
      0 < u x + ε := by
    have hsub : originCube (d := d) R ⊆ originCube 1 :=
      Assembly.caccioppoli_cube_mono hR
    exact ae_restrict_of_ae_restrict_of_subset hsub hUposOne
  have hWposR : ∀ᵐ x ∂(volume.restrict (originCube (d := d) R)), 0 < W x := by
    filter_upwards [hUposR] with x hx
    simp only [W]
    split_ifs <;> positivity
  let v : Vec d → ℝ := fun x => (u x + ε) ^ (z / r)
  have hpowρ : v =ᵐ[volume.restrict (originCube ρ)]
      (fun x => Real.rpow (W x) sm) := by
    have hsub : originCube (d := d) ρ ⊆ originCube (d := d) 1 :=
      Assembly.caccioppoli_cube_mono (by linarith : ρ ≤ 1)
    have hUposρ := ae_restrict_of_ae_restrict_of_subset hsub hUposOne
    filter_upwards [hUposρ] with x hx
    by_cases hzpos : 0 < z
    · have habs : |z| = z := abs_of_pos hzpos
      have hexp : z / r = |z| / r := by rw [habs]
      simp only [v, W, ite_eq_left hzpos, sm, hexp]
      rfl
    · have hzneg : z < 0 := by
        rcases eq_or_lt_of_le (le_of_not_gt hzpos) with heq | hlt
        · exact (hz heq).elim
        · exact hlt
      have hexp : z / r = -( |z| / r) := by rw [abs_of_neg hzneg]; ring
      simp only [v, W, ite_eq_right hzpos, sm]
      rw [hexp, Real.rpow_neg_eq_inv_rpow]
      rfl
  have hpowR : v =ᵐ[volume.restrict (originCube R)]
      (fun x => Real.rpow (W x) sm) := by
    filter_upwards [hUposR] with x hx
    by_cases hzpos : 0 < z
    · have habs : |z| = z := abs_of_pos hzpos
      have hexp : z / r = |z| / r := by rw [habs]
      simp only [v, W, ite_eq_left hzpos, sm, hexp]
      rfl
    · have hzneg : z < 0 := by
        rcases eq_or_lt_of_le (le_of_not_gt hzpos) with heq | hlt
        · exact (hz heq).elim
        · exact hlt
      have hexp : z / r = -( |z| / r) := by rw [abs_of_neg hzneg]; ring
      simp only [v, W, ite_eq_right hzpos, sm]
      rw [hexp, Real.rpow_neg_eq_inv_rpow]
      rfl
  have hρmeas := measurable_originCube (d := d) ρ
  have hRmeas := measurable_originCube (d := d) R
  have hρW := normalizedLpMoment_congr_ae (originCube ρ) hρmeas v
    (fun x => Real.rpow (W x) sm) (rStarPos) hpowρ
  have hRW := normalizedLpMoment_congr_ae (originCube R) hRmeas v
    (fun x => Real.rpow (W x) sm) rPos hpowR
  have hρscale := normalizedLpMoment_rpow_scale (originCube ρ) hρmeas W
    rStarPos hsm (by
      have hWposρ := ae_restrict_of_ae_restrict_of_subset
        (Assembly.caccioppoli_cube_mono (by linarith : ρ ≤ R)) hWposR
      exact hWposρ)
  have hRscale := normalizedLpMoment_rpow_scale (originCube R) hRmeas W
    rPos hsm hWposR
  have hrStarExp : rStar * sm = χ * |z| := by
    dsimp [χ, sm]
    field_simp [ne_of_gt rPos]
  have hrExp : sm * r = |z| := by
    dsimp [sm]
    field_simp [ne_of_gt rPos]
  have hρid :
      (CoarseDeGiorgi.normalizedLpMoment rStar rStarPos (originCube ρ) v) ^ r =
        (CoarseDeGiorgi.normalizedLpMoment (χ * |z|)
          (mul_pos (by positivity : 0 < χ) (abs_pos.mpr hz))
          (originCube ρ) W) ^ |z| := by
    calc
      _ = (CoarseDeGiorgi.normalizedLpMoment rStar rStarPos
          (originCube ρ) (fun x => Real.rpow (W x) sm)) ^ r := by rw [hρW]
      _ = ((CoarseDeGiorgi.normalizedLpMoment (rStar * sm)
          (mul_pos rStarPos hsm) (originCube ρ) W) ^ sm) ^ r := by
            rw [hρscale]
      _ = _ := by
        rw [← ENNReal.rpow_mul]
        simp only [hrStarExp, hrExp]
  have hRid :
      (CoarseDeGiorgi.normalizedLpMoment r rPos (originCube R) v) ^ r =
        (CoarseDeGiorgi.normalizedLpMoment |z| (abs_pos.mpr hz)
          (originCube R) W) ^ |z| := by
    calc
      _ = (CoarseDeGiorgi.normalizedLpMoment r rPos
          (originCube R) (fun x => Real.rpow (W x) sm)) ^ r := by rw [hRW]
      _ = ((CoarseDeGiorgi.normalizedLpMoment (r * sm)
          (mul_pos rPos hsm) (originCube R) W) ^ sm) ^ r := by
            rw [hRscale]
      _ = _ := by
        rw [← ENNReal.rpow_mul]
        simp only [mul_comm r sm, hrExp]
  have hrz' : z < (1 / 2 : ℝ) * r := by
    calc
      z < paramR q / 2 := hzr
      _ = (1 / 2 : ℝ) * r := by dsimp [r]; ring
  have hm : z / r < 1 / 2 := (div_lt_iff₀ rPos).2 hrz'
  have hstep := hReverse (z / r) hm
    (div_ne_zero hz rPos.ne')
    ρ R hρ hρR hR
  have hstep' := hstep
  dsimp only [r, rStar, v] at hstep'
  rw [hρid, hRid] at hstep'
  simpa only [v, r, rStar, χ, W] using hstep'

end CoarseDeGiorgi.Harnack.Iterations
