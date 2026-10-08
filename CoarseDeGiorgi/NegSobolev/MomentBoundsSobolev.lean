module

public import CoarseDeGiorgi.Statements.MomentBoundsBesov
public import CoarseDeGiorgi.Statements.NegSobolevNorm
public import CoarseDeGiorgi.Statements.IsOpenOriginCube

/-! The Sobolev moment bounds, conditional on `l.negative.sobolev`. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace CoarseDeGiorgi.NegSobolev

lemma besov_moment_factor_le (d : ℕ) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2) ≤
      ENNReal.ofReal (d.factorial : ℝ) := by
  apply ENNReal.ofReal_le_ofReal
  have hpos := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-s)
  have hone := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3)
    (neg_nonpos.mpr hs.le)
  have square_le_one (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (1 - x) ^ 2 ≤ 1 := by
    nlinarith only [hx0, hx1, mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hsq : (1 - Real.rpow 3 (-s)) ^ 2 ≤ 1 := square_le_one _ hpos hone
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d.factorial)

/-- `c.negative.sobolev`, assuming the exact universally quantified statement of `l.negative.sobolev`. -/
theorem moment_bounds_sobolev_of_negative_sobolev_bound
    (hB2 : ∀ (d : ℕ) (p s ε : ℝ)
    (hp : 1 < p) (hs : 0 < s) (_hε : 0 < ε) (hεs : ε ≤ 2 * s),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Vec d → Mat d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), (b x).PosSemidef) →
        ∀ (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1))),
          besovCubeNorm b hb s p hs hp.le ≤
            ENNReal.ofReal C *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) b hb (2 * s - ε) p (sub_nonneg.mpr hεs) hp)
    (d : ℕ) (_hd : 3 ≤ d) (p q s t ε : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hε : 0 < ε) (hεs : ε ≤ 2 * s) (hεt : ε ≤ 2 * t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
        (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1))),
        negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA (2 * s - ε) p (sub_nonneg.mpr hεs) hp < ⊤ →
        negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv (2 * t - ε) q
          (sub_nonneg.mpr hεt) hq < ⊤ →
        upperMoment a ha s p hs hp.le ≤
            ENNReal.ofReal C *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA (2 * s - ε) p (sub_nonneg.mpr hεs) hp ∧
          (lowerMoment a ha t q ht hq.le)⁻¹ ≤
            ENNReal.ofReal C *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv (2 * t - ε) q
                (sub_nonneg.mpr hεt) hq ∧
          contrast a ha s t p q hs ht hp.le hq.le ≤
            ENNReal.ofReal (C ^ 2) *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA (2 * s - ε) p (sub_nonneg.mpr hεs) hp *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv (2 * t - ε) q
                (sub_nonneg.mpr hεt) hq := by
  obtain ⟨C₁, hC₁, hB₁⟩ := hB2 d p s ε hp hs _hε hεs
  obtain ⟨C₂, hC₂, hB₂⟩ := hB2 d q t ε hq ht _hε hεt
  let K := max C₁ C₂
  have hK : 0 ≤ K := hC₁.trans (le_max_left _ _)
  refine ⟨(d.factorial : ℝ) * K, mul_nonneg (Nat.cast_nonneg _) hK, ?_⟩
  intro a ha hA hAinv hN₁ hN₂
  have hpos : ∀ᵐ x ∂volume.restrict (originCube 1), (a x).PosSemidef :=
    ha.2.1.mono (fun _ hx => hx.posSemidef)
  have hinv : ∀ᵐ x ∂volume.restrict (originCube 1), ((a x)⁻¹).PosSemidef :=
    ha.2.1.mono (fun _ hx => hx.inv.posSemidef)
  have h₁ := (hB₁ a hpos hA).trans (mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (le_max_left C₁ C₂)) _)
  have h₂ := (hB₂ (fun x => (a x)⁻¹) hinv hAinv).trans (mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (le_max_right C₁ C₂)) _)
  have hb₁ : besovCubeNorm a hA s p hs hp.le < ⊤ :=
    h₁.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN₁)
  have hb₂ : besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le < ⊤ :=
    h₂.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN₂)
  obtain ⟨hm₁, hm₂, hm₃⟩ := CoarseDeGiorgi.moment_bounds_besov d _hd p q s t
    hp hq hs ht a ha hA hAinv hb₁ hb₂
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ENNReal.ofReal (d.factorial : ℝ) * besovCubeNorm a hA s p hs hp.le :=
        hm₁.trans (mul_le_mul_left (besov_moment_factor_le d hs) _)
      _ ≤ ENNReal.ofReal (d.factorial : ℝ) * (ENNReal.ofReal K * _) :=
        mul_le_mul_right h₁ _
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  · calc
      _ ≤ ENNReal.ofReal (d.factorial : ℝ) *
          besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le :=
        hm₂.trans (mul_le_mul_left (besov_moment_factor_le d ht) _)
      _ ≤ ENNReal.ofReal (d.factorial : ℝ) * (ENNReal.ofReal K * _) :=
        mul_le_mul_right h₂ _
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  · calc
      _ ≤ ENNReal.ofReal ((d.factorial : ℝ) ^ 2) *
          besovCubeNorm a hA s p hs hp.le *
          besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le := hm₃
      _ ≤ ENNReal.ofReal ((d.factorial : ℝ) ^ 2) *
          (ENNReal.ofReal K * _) * (ENNReal.ofReal K * _) :=
        mul_le_mul (mul_le_mul_right h₁ _) h₂ zero_le zero_le
      _ = _ := by
        rw [ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ENNReal.ofReal_pow (mul_nonneg (Nat.cast_nonneg _) hK),
          ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        ring

end CoarseDeGiorgi.NegSobolev
