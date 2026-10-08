module

public import CoarseDeGiorgi.Harnack.ReverseMoments.ReverseNorm
public import CoarseDeGiorgi.Harnack.ReverseMoments.MomentConversion
public import CoarseDeGiorgi.Harnack.Powers.SignedPower
public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import CoarseDeGiorgi.Assembly.HybridParameters

@[expose] public section

namespace CoarseDeGiorgi.Harnack.ReverseMoments

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

theorem paramR_pos_of_harnack_facts {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) : 0 < paramR q := by
  obtain ⟨_, _, hr, _, _, _, _, _⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  exact zero_lt_one.trans hr

theorem rStarParam_pos_of_harnack_facts {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) : 0 < rStarParam (d := d) q t := by
  obtain ⟨_, _, hr, _, _, _, _, hstar⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  exact lt_trans (zero_lt_one.trans hr) hstar

private theorem chiParam_ge_one_of_harnack_facts {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) : 1 ≤ chiParam (d := d) q t := by
  obtain ⟨_, _, hr, _, _, _, _, hstar⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hrPos : 0 < paramR q := zero_lt_one.trans hr
  have hχ : 1 < rStarParam (d := d) q t / paramR q :=
    (lt_div_iff₀ hrPos).2 (by simpa using hstar)
  simpa [chiParam] using hχ.le

/-- A normalized one-step reverse-Hölder estimate for the signed shifted
powers. The exact power-Caccioppoli contract is supplied as an explicit
input. Its `L^{r*}` to `L^r` norm estimate is raised to `r` and
normalized; the only radius-independent loss is absorbed into `C`. -/
theorem signed_power_normalized_reverse_of_power_caccioppoli
    (hPowerCaccioppoli :
      ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
        (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
        0 < paramTheta d p q s t →
        ∃ C : ℝ≥0∞, C < ⊤ ∧
          ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
            spatialMomentRange a ha p q s t →
            ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
              (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
              IsWeightedSupersolution a (originCube 1) u G →
              ∀ ε : ℝ, 0 < ε →
                ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
                  ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                    weightedEnergy a (originCube ρ)
                      (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                      C * (ENNReal.ofReal (R - ρ)).rpow
                          (-2 * gammaTwoParam (d := d) p q t * alphaParam t /
                            paramTheta d p q s t) *
                        upperMoment a ha s p hs (le_of_lt hp) *
                        ENNReal.ofReal (powerFactor m ^ 2) *
                        (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                          contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                          (sigmaParam (d := d) p q s / paramTheta d p q s t) *
                        (eLpNorm (fun x => (u x + ε) ^ m)
                          (ENNReal.ofReal (paramR q))
                          (volume.restrict (originCube R))).rpow 2)
    {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ≥0∞, 1 ≤ C ∧ C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε →
            ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
              ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                let v : Vec d → ℝ := fun x => (u x + ε) ^ m
                (CoarseDeGiorgi.normalizedLpMoment
                    (rStarParam (d := d) q t)
                    (rStarParam_pos_of_harnack_facts hd hp hq hs ht hθ)
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
                      (paramR_pos_of_harnack_facts hd hp hq hs ht hθ)
                      (originCube R) v) ^ (paramR q) := by
  obtain ⟨C₀, hC₀, hC₀top, hReverseNorm⟩ :=
    signed_power_reverse_norm_of_power_caccioppoli hPowerCaccioppoli
      hd hp hq hs ht hθ
  let r : ℝ := paramR q
  let rStar : ℝ := rStarParam (d := d) q t
  let chi : ℝ := chiParam (d := d) q t
  let K : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ d)
  let C : ℝ≥0∞ := 1 + K * C₀ ^ r
  have hr : 0 < r := paramR_pos_of_harnack_facts hd hp hq hs ht hθ
  have hrStar : 0 < rStar := rStarParam_pos_of_harnack_facts hd hp hq hs ht hθ
  have hchi : 1 ≤ chi := by
    simpa only [chi] using chiParam_ge_one_of_harnack_facts hd hp hq hs ht hθ
  have hC₀powTop : C₀ ^ r < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hr.le hC₀top.ne
  have hKtop : K < ⊤ := by simp [K]
  have hKpowTop : K * C₀ ^ r < ⊤ := ENNReal.mul_lt_top hKtop hC₀powTop
  have hCpos : 1 ≤ C := by dsimp [C]; exact le_add_right le_rfl
  have hCtop : C < ⊤ := by
    dsimp [C]
    exact ENNReal.add_lt_top.mpr ⟨by simp, hKpowTop⟩
  refine ⟨C, hCpos, hCtop, ?_⟩
  intro a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  let gap : ℝ := (R - ρ) / 2
  let γ₅ : ℝ := gammaOneParam (d := d) q t +
    gammaTwoParam (d := d) p q t * alphaParam t / paramTheta d p q s t
  let η : ℝ := alphaParam t / (2 * paramTheta d p q s t)
  let F : ℝ≥0∞ := ENNReal.ofReal (powerFactor m ^ 2)
  let Θ : ℝ≥0∞ := contrast a ha s t p q hs ht hp.le hq.le
  let X : ℝ≥0∞ := 1 + F * Θ
  let v : Vec d → ℝ := fun x => (u x + ε) ^ m
  have hρpos : 0 < ρ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hρ
  have hRpos : 0 < R :=
    lt_trans (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hρ) hρR
  have hρ1 : ρ ≤ 1 := hρR.le.trans hR
  have hunit := Assembly.hybrid_unitCube_domain (d := d)
  have : NeZero d := ⟨by omega⟩
  change IsWeightedSubsolution a (originCube 1) (-u) (-G) at hsup
  have hmemU : MemH1a a (originCube 1) u G := by
    have h := Weighted.MemH1a.neg hunit.1 hunit.2 ha hsup.1
    simpa only [Pi.neg_apply, neg_neg] using h
  have hparams := Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  obtain ⟨_, _, hr1, hr2, _, _, _, hstar⟩ := hparams
  have hpower := Powers.signedPower_source_package hunit.1 hunit.2 ha hmemU hsup
    hnonneg ε m (paramR q) hε hm hm0 hr1 hr2
  have hvMeas : AEStronglyMeasurable v (volume.restrict (originCube 1)) := by
    simpa only [v] using hpower.1.1
  have hvρ : AEStronglyMeasurable v (volume.restrict (originCube ρ)) :=
    hvMeas.mono_measure
      (Measure.restrict_mono (Assembly.caccioppoli_cube_mono hρ1) le_rfl)
  have hvR : AEStronglyMeasurable v (volume.restrict (originCube R)) :=
    hvMeas.mono_measure
      (Measure.restrict_mono (Assembly.caccioppoli_cube_mono hR) le_rfl)
  have hμρ0 : (volume.restrict (originCube (d := d) ρ)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ, originCube_volume (d := d) ρ hρpos.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hρpos d)).ne'
  have hμρtop : (volume.restrict (originCube (d := d) ρ)) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ, originCube_volume (d := d) ρ hρpos.le]
    exact ENNReal.ofReal_ne_top
  have hμR0 : (volume.restrict (originCube (d := d) R)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ, originCube_volume (d := d) R hRpos.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hRpos d)).ne'
  have hμRtop : (volume.restrict (originCube (d := d) R)) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ, originCube_volume (d := d) R hRpos.le]
    exact ENNReal.ofReal_ne_top
  have hgapPos : 0 < gap := by dsimp [gap]; linarith
  have hvolExponent : -r / rStar = -1 / chi := by
    dsimp [r, rStar, chi]
    unfold chiParam
    field_simp [hr.ne', hrStar.ne']
  have hvolume : (volume.restrict (originCube (d := d) ρ) Set.univ) ^ (-r / rStar) *
      (volume.restrict (originCube (d := d) R) Set.univ) ≤ K := by
    simpa only [K, hvolExponent] using
      originCube_normalization_factor_le hρ hRpos hR hchi
  have hgapNorm : ENNReal.ofReal (gap ^ (-γ₅)) =
      ENNReal.ofReal (gap ^ (-gammaOneParam (d := d) q t -
        gammaTwoParam (d := d) p q t * alphaParam t /
          paramTheta d p q s t)) := by
    congr 1
    dsimp [γ₅]
    ring_nf
  let B : ℝ≥0∞ := C₀ * ENNReal.ofReal (gap ^ (-γ₅)) * X ^ η
  have hnorm : eLpNorm v (ENNReal.ofReal rStar) (volume.restrict (originCube ρ)) ≤
      B * eLpNorm v (ENNReal.ofReal r) (volume.restrict (originCube R)) := by
    have h := hReverseNorm a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
    simpa only [v, rStar, r, B, gap, γ₅, η, F, Θ, X, hgapNorm,
      ENNReal.rpow_eq_pow] using h
  have hnormalized := normalizedLpMoment_reverse_of_eLpNorm
    (originCube ρ) (originCube R) v hrStar hr hvρ hvR
    hμρ0 hμρtop hμR0 hμRtop K B hvolume hnorm
  have hBpow : B ^ r = C₀ ^ r *
      (ENNReal.ofReal (gap ^ (-γ₅))) ^ r * X ^ (η * r) := by
    dsimp [B]
    calc
      _ = (C₀ ^ r * (ENNReal.ofReal (gap ^ (-γ₅))) ^ r) *
          (X ^ η) ^ r := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,
              ENNReal.mul_rpow_of_nonneg C₀ _ hr.le]
      _ = _ := by rw [ENNReal.rpow_mul]
  have hcoeff : K * C₀ ^ r ≤ C := by
    dsimp [C]
    exact le_add_left le_rfl
  have hηr : η * r = alphaParam t * paramR q /
      (2 * paramTheta d p q s t) := by
    dsimp [η, r]
    ring_nf
  calc
    _ ≤ K * B ^ r *
        (CoarseDeGiorgi.normalizedLpMoment r
          (paramR_pos_of_harnack_facts hd hp hq hs ht hθ)
          (originCube R) v) ^ r := hnormalized
    _ ≤ C * (ENNReal.ofReal (gap ^ (-γ₅))) ^ r * X ^ (η * r) *
        (CoarseDeGiorgi.normalizedLpMoment r
          (paramR_pos_of_harnack_facts hd hp hq hs ht hθ)
          (originCube R) v) ^ r := by
      rw [hBpow]
      have hc := mul_le_mul_of_nonneg_right hcoeff
        (by positivity : 0 ≤ (ENNReal.ofReal (gap ^ (-γ₅))) ^ r *
          X ^ (η * r))
      exact mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using hc) (by positivity)
    _ = _ := by
      rw [hηr]
      simp [gap, γ₅, X, F, Θ, v, r,
        ENNReal.rpow_eq_pow]

end

end CoarseDeGiorgi.Harnack.ReverseMoments
