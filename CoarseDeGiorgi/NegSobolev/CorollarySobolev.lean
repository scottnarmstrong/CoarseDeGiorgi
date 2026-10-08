import CoarseDeGiorgi.Statements.LocalBoundedness
import CoarseDeGiorgi.Statements.Harnack
import CoarseDeGiorgi.Statements.NegSobolevNorm
import CoarseDeGiorgi.Statements.IsOpenOriginCube

/-! `c.sobolev.coefficients`, conditional on the Sobolev moment theorem. -/
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace CoarseDeGiorgi.NegSobolev

/-- The local boundedness part of `c.sobolev.coefficients`, assuming the exact statement of `c.negative.sobolev`. -/
theorem local_boundedness_sobolev_of_moment_bounds
    (hMom : ∀ (d : ℕ) (_hd : 3 ≤ d) (p q s t ε : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hε : 0 < ε) (hεs : ε ≤ 2 * s) (hεt : ε ≤ 2 * t),
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
                (sub_nonneg.mpr hεt) hq)
    (d : ℕ) (_hd : 3 ≤ d) (p q α β : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (θ : ℝ) (_hθdef : θ = 1 - (α + β) / 2 - ((d : ℝ) - 1) / 2 * (1 / p + 1 / q))
    (_hθ : 0 < θ) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧
      ∀ (a : CoeffField d), IsWeightedCoeffOn (originCube 1) a →
      ∀ (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1))),
        negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp < ⊤ →
        negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq < ⊤ →
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
        IsWeightedSubsolution a (originCube 1) u G →
        ∀ (ρ₁ ρ₂ : ℝ), 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        let rhs := ENNReal.ofReal C *
          (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-γ) *
          (negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
            negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq).rpow
              ((d - 1 : ℝ) / (2 * θ)) *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ₂))
        eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ₁)) ≤ rhs ∧
          (ρ₂ < 1 → eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ₂)) < ⊤) := by
  let s := α / 2 + θ / 4
  let t := β / 2 + θ / 4
  have hs : 0 < s := by dsimp [s]; linarith only [hα, _hθ]
  have ht : 0 < t := by dsimp [t]; linarith only [hβ, _hθ]
  have hε : 0 < θ / 2 := half_pos _hθ
  have hεs : θ / 2 ≤ 2 * s := by dsimp [s]; linarith only [hα]
  have hεt : θ / 2 ≤ 2 * t := by dsimp [t]; linarith only [hβ]
  have horder₁ : 2 * s - θ / 2 = α := by dsimp [s]; ring
  have horder₂ : 2 * t - θ / 2 = β := by dsimp [t]; ring
  have hparam : paramTheta d p q s t = θ / 2 := by
    unfold paramTheta
    dsimp [s, t]
    linarith only [_hθdef]
  have hparampos : 0 < paramTheta d p q s t := hparam.symm ▸ hε
  obtain ⟨M, hM, hbounds⟩ := hMom d _hd p q s t (θ / 2) hp hq hs ht hε hεs hεt
  obtain ⟨γ, hγ, ⟨⟨A, hAnonneg, hlocal⟩, _⟩⟩ :=
    CoarseDeGiorgi.local_boundedness d _hd p q s t hp hq hs ht hparampos
  let r := (d - 1 : ℝ) / (2 * θ)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hd1) (by positivity)
  have hexp : (d - 1 : ℝ) / (4 * paramTheta d p q s t) = r := by
    rw [hparam]
    dsimp [r]
    congr 1
    ring
  refine ⟨A * (M ^ 2) ^ r, γ, mul_nonneg hAnonneg (Real.rpow_nonneg (sq_nonneg _) _), hγ, ?_⟩
  intro a ha hA hAinv hN₁ hN₂
  have hbounds' := hbounds a ha hA hAinv
  simp only [horder₁, horder₂] at hbounds'
  obtain ⟨hm₁, hm₂, hm₃⟩ := hbounds' hN₁ hN₂
  have hupper : upperMoment a ha s p hs hp.le < ⊤ :=
    hm₁.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN₁)
  have hlower : 0 < lowerMoment a ha t q ht hq.le :=
    ENNReal.inv_lt_top.mp (hm₂.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN₂))
  intro u G hsub ρ₁ ρ₂ hρ₁ hρ hρ₂
  have hlocal' := (hlocal a ha hupper hlower u G hsub).2 ρ₁ ρ₂ hρ₁ hρ hρ₂
  dsimp only at hlocal' ⊢
  rw [hexp] at hlocal'
  refine ⟨hlocal'.1.trans ?_, hlocal'.2⟩
  have hc : contrast a ha s t p q hs ht hp.le hq.le ≤
      ENNReal.ofReal (M ^ 2) *
        (negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
          negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹)
            hAinv β q hβ hq) := by simpa only [mul_assoc] using hm₃
  calc
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-γ) *
        (ENNReal.ofReal (M ^ 2) *
          (negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
            negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹)
              hAinv β q hβ hq)).rpow r *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ₂)) := by
      gcongr
      exact ENNReal.rpow_le_rpow hc hr
    _ = _ := by
      change _ = ENNReal.ofReal (A * (M ^ 2) ^ r) *
        (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-γ) *
        (negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
          negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹)
            hAinv β q hβ hq).rpow r *
        eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ₂))
      simp only [ENNReal.rpow_eq_pow, ENNReal.mul_rpow_of_nonneg _ _ hr,
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg M) hr,
        ENNReal.ofReal_mul hAnonneg]
      ring

/-- The Harnack part of `c.sobolev.coefficients`, assuming the exact statement of `c.negative.sobolev`. -/
theorem harnack_sobolev_of_moment_bounds
    (hMom : ∀ (d : ℕ) (_hd : 3 ≤ d) (p q s t ε : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hε : 0 < ε) (hεs : ε ≤ 2 * s) (hεt : ε ≤ 2 * t),
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
                (sub_nonneg.mpr hεt) hq)
    (d : ℕ) (_hd : 3 ≤ d) (p q α β : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (θ : ℝ) (_hθdef : θ = 1 - (α + β) / 2 - ((d : ℝ) - 1) / 2 * (1 / p + 1 / q))
    (_hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffField d), IsWeightedCoeffOn (originCube 1) a →
      ∀ (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1))),
        negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp < ⊤ →
        negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq < ⊤ →
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
        IsWeightedSolution a (originCube 1) u G →
        eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt
            (negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq).toReal)) *
            nonnegativeEssInf (originCube (1 / 2)) u := by
  let s := α / 2 + θ / 4
  let t := β / 2 + θ / 4
  have hs : 0 < s := by dsimp [s]; linarith only [hα, _hθ]
  have ht : 0 < t := by dsimp [t]; linarith only [hβ, _hθ]
  have hε : 0 < θ / 2 := half_pos _hθ
  have hεs : θ / 2 ≤ 2 * s := by dsimp [s]; linarith only [hα]
  have hεt : θ / 2 ≤ 2 * t := by dsimp [t]; linarith only [hβ]
  have horder₁ : 2 * s - θ / 2 = α := by dsimp [s]; ring
  have horder₂ : 2 * t - θ / 2 = β := by dsimp [t]; ring
  have hparam : paramTheta d p q s t = θ / 2 := by
    unfold paramTheta
    dsimp [s, t]
    linarith only [_hθdef]
  have hparampos : 0 < paramTheta d p q s t := hparam.symm ▸ hε
  obtain ⟨M, hM, hbounds⟩ := hMom d _hd p q s t (θ / 2) hp hq hs ht hε hεs hεt
  obtain ⟨A, hAnonneg, hharnack⟩ :=
    CoarseDeGiorgi.harnack d _hd p q s t hp hq hs ht hparampos
  refine ⟨A * M, mul_nonneg hAnonneg hM, ?_⟩
  intro a ha hA hAinv hN₁ hN₂
  have hbounds' := hbounds a ha hA hAinv
  simp only [horder₁, horder₂] at hbounds'
  obtain ⟨hm₁, hm₂, hm₃⟩ := hbounds' hN₁ hN₂
  have hupper : upperMoment a ha s p hs hp.le < ⊤ :=
    hm₁.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN₁)
  have hlower : 0 < lowerMoment a ha t q ht hq.le :=
    ENNReal.inv_lt_top.mp (hm₂.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN₂))
  intro u G hu hsol
  have hh := hharnack a ha hupper hlower u G hu hsol
  apply hh.trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hfinite : ENNReal.ofReal (M ^ 2) *
      negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
        negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹)
          hAinv β q hβ hq < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN₁) hN₂
  have hc := ENNReal.toReal_mono hfinite.ne hm₃
  have hsqrt := Real.sqrt_le_sqrt hc
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg M),
    mul_assoc, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM] at hsqrt
  have hb := mul_le_mul_of_nonneg_left hsqrt hAnonneg
  simpa only [ENNReal.toReal_mul, mul_assoc] using hb

end CoarseDeGiorgi.NegSobolev
