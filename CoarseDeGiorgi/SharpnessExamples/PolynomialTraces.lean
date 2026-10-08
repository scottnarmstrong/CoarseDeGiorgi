module

public import CoarseDeGiorgi.SharpnessExamples.PolynomialEllipticity
public import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem polynomialNatPow_eq_rpow {d : ℕ} (hd : 1 ≤ d) (x : ℝ) :
    x ^ (d - 1 : ℕ) = Real.rpow x ((d : ℝ) - 1) := by
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]
    norm_num
  calc
    x ^ (d - 1 : ℕ) = Real.rpow x ((d - 1 : ℕ) : ℝ) :=
      (Real.rpow_natCast x (d - 1)).symm
    _ = Real.rpow x ((d : ℝ) - 1) := congrArg _ hcast

private theorem polynomialParallel_volume_power_le {d : ℕ} {q t epsilon : ℝ}
    (hd : 3 ≤ d) (hTpos : 0 < polynomialHatT d q t)
    (hTlt : polynomialHatT d q t < 1) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) :
    polynomialParallel d q t epsilon * epsilon ^ (d - 1 : ℕ) ≤ (d : ℝ) - 1 := by
  have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : 0 < ((d : ℝ) - 3) + 2 * polynomialHatT d q t := by linarith
  have hpow : Real.rpow epsilon (((d : ℝ) - 3) + 2 * polynomialHatT d q t) ≤ 1 := by
    simpa only [Real.rpow_eq_pow, Real.one_rpow] using
      (Real.rpow_le_rpow hepsilon.le hepsilon1 hexp.le)
  have hprod : Real.rpow epsilon (2 * polynomialHatT d q t - 2) *
      Real.rpow epsilon ((d : ℝ) - 1) =
        Real.rpow epsilon (((d : ℝ) - 3) + 2 * polynomialHatT d q t) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hepsilon]
    congr 1
    ring
  calc
    polynomialParallel d q t epsilon * epsilon ^ (d - 1 : ℕ) =
        ((d : ℝ) - 1) *
          (Real.rpow epsilon (2 * polynomialHatT d q t - 2) *
            Real.rpow epsilon ((d : ℝ) - 1)) := by
          simp [polynomialParallel, polynomialNatPow_eq_rpow (by omega : 1 ≤ d)]
          ring
    _ = ((d : ℝ) - 1) *
        Real.rpow epsilon (((d : ℝ) - 3) + 2 * polynomialHatT d q t) := by rw [hprod]
    _ ≤ (d : ℝ) - 1 := by
      calc
        _ ≤ ((d : ℝ) - 1) * 1 :=
          mul_le_mul_of_nonneg_left hpow (by linarith)
        _ = (d : ℝ) - 1 := by ring

private theorem polynomialPerpendicularInv_volume_power_le {d : ℕ} {q t epsilon : ℝ}
    (hd : 3 ≤ d) (hTlt : polynomialHatT d q t < 1)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (polynomialPerpendicular d q t epsilon)⁻¹ * epsilon ^ (d - 1 : ℕ) ≤ 1 := by
  have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp : 0 < ((d : ℝ) - 1) - 2 * polynomialHatT d q t := by linarith
  have hpow : Real.rpow epsilon (((d : ℝ) - 1) - 2 * polynomialHatT d q t) ≤ 1 := by
    simpa only [Real.rpow_eq_pow, Real.one_rpow] using
      (Real.rpow_le_rpow hepsilon.le hepsilon1 hexp.le)
  have hprod : Real.rpow epsilon (-2 * polynomialHatT d q t) *
      Real.rpow epsilon ((d : ℝ) - 1) =
        Real.rpow epsilon (((d : ℝ) - 1) - 2 * polynomialHatT d q t) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hepsilon]
    congr 1
    ring
  have hinv : (polynomialPerpendicular d q t epsilon)⁻¹ =
      Real.rpow epsilon (-2 * polynomialHatT d q t) := by
    unfold polynomialPerpendicular
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_neg hepsilon.le]
    congr 1
    ring
  calc
    (polynomialPerpendicular d q t epsilon)⁻¹ * epsilon ^ (d - 1 : ℕ) =
        Real.rpow epsilon (-2 * polynomialHatT d q t) *
          Real.rpow epsilon ((d : ℝ) - 1) := by
          rw [hinv, polynomialNatPow_eq_rpow (by omega : 1 ≤ d)]
    _ = Real.rpow epsilon (((d : ℝ) - 1) - 2 * polynomialHatT d q t) := hprod
    _ ≤ 1 := hpow

private theorem polynomialDiagonal_trace_le {d : ℕ} (b : Fin d → ℝ) (M : ℝ)
    (hb : ∀ i, b i ≤ M) : (Matrix.diagonal b : Mat d).trace ≤ (d : ℝ) * M := by
  rw [Matrix.trace_diagonal]
  calc
    ∑ i, b i ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hb i
    _ = (d : ℝ) * M := by simp

private theorem polynomialCube_volume_one {d : ℕ} :
    volume (originCube (d := d) 1) = 1 := by
  have he : originCube (d := d) 1 =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp [originCube, Set.mem_pi]
  rw [he, Real.volume_pi_Ioo]
  norm_num

private theorem polynomialCube_measurable {d : ℕ} :
    MeasurableSet (originCube (d := d) 1) := by
  have he : originCube (d := d) 1 =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp [originCube, Set.mem_pi]
  rw [he]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

private theorem polynomialTube_indicator_integral {d : ℕ} (epsilon : ℝ) :
    (∫ x in originCube (d := d) 1,
      (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x) =
        (volume (originCube (d := d) 1 ∩ responseCylinder epsilon)).toReal := by
  have hvol := polynomialCube_volume_one (d := d)
  calc
    _ = Homogenization.volumeAverage (originCube 1)
        ((responseCylinder epsilon).indicator (fun _ => (1 : ℝ))) := by
          unfold Homogenization.volumeAverage
          rw [hvol]
          simp
    _ = (volume (originCube 1 ∩ responseCylinder epsilon)).toReal /
        (volume (originCube 1)).toReal :=
          cylinderResponseFraction_eq_volume (originCube 1) epsilon
    _ = _ := by rw [hvol]; norm_num

/-- The integral of the coefficient and inverse traces is uniformly bounded
over the polynomial cylinder family. -/
theorem polynomialCoefficientFamily_trace_integral_bound {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ, ∀ epsilon, 0 < epsilon → epsilon < 1 / 8 →
      ∫ x in originCube (d := d) 1,
        ((polynomialCoefficientFamily d q t epsilon x).trace +
          ((polynomialCoefficientFamily d q t epsilon x)⁻¹).trace) ≤ C := by
  have hTpos := polynomialHatT_pos (by omega : 2 ≤ d) hq ht
  have hTlt := polynomialHatT_lt_one hd hp hs hθ
  let C : ℝ := 2 * (d : ℝ) + 2 * (d : ℝ) * 4 ^ (d - 1) * (d : ℝ)
  refine ⟨C, ?_⟩
  intro epsilon hepsilon hepsilon8
  let lam := polynomialPerpendicular d q t epsilon
  let Λ := polynomialParallel d q t epsilon
  have hlam : 0 < lam := polynomialPerpendicular_pos hepsilon
  have hlam1 : lam ≤ 1 := by
    have hpow := Real.rpow_le_rpow hepsilon.le (by linarith : epsilon ≤ 1)
      (by linarith : 0 ≤ 2 * polynomialHatT d q t)
    dsimp [lam, polynomialPerpendicular]
    simpa only [Real.rpow_eq_pow, Real.one_rpow] using hpow
  have hΛ : 0 < Λ := by
    dsimp [Λ, polynomialParallel]
    have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hd' : 0 < (d : ℝ) - 1 := by linarith
    exact mul_pos hd' (Real.rpow_pos_of_pos hepsilon _)
  have hΛ1 : 1 ≤ Λ := by
    have hexp : 2 * polynomialHatT d q t - 2 ≤ 0 := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hepsilon (by linarith : epsilon ≤ 1) hexp
    have hpow' : 1 ≤ Real.rpow epsilon (2 * polynomialHatT d q t - 2) := by
      change 1 ≤ epsilon ^ (2 * polynomialHatT d q t - 2)
      simpa only [Real.one_rpow] using hpow
    have hfactor : 1 ≤ (d : ℝ) - 1 := by
      have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    dsimp [Λ, polynomialParallel]
    calc
      1 ≤ (d : ℝ) - 1 := hfactor
      _ ≤ ((d : ℝ) - 1) * Real.rpow epsilon (2 * polynomialHatT d q t - 2) := by
        calc
          _ = ((d : ℝ) - 1) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow' (by linarith)
  have hAvol := polynomialParallel_volume_power_le hd hTpos hTlt hepsilon
    (by linarith : epsilon ≤ 1)
  have hBvol := polynomialPerpendicularInv_volume_power_le hd hTlt hepsilon
    (by linarith : epsilon ≤ 1)
  let V := originCube (d := d) 1
  have hVmeas : MeasurableSet V := by
    dsimp [V]
    exact polynomialCube_measurable
  let f : Vec d → ℝ := fun x =>
    (polynomialCoefficientFamily d q t epsilon x).trace +
      ((polynomialCoefficientFamily d q t epsilon x)⁻¹).trace
  let g : Vec d → ℝ := fun x => 2 * (d : ℝ) +
    (d : ℝ) * (Λ + lam⁻¹) * (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x
  have ha : IsWeightedCoeffOn V (polynomialCoefficientFamily d q t epsilon) :=
    polynomialCoefficientFamily_weightedCoeffOn (by omega : 2 ≤ d) q t epsilon
  have hf : IntegrableOn f V := by
    exact (ha.2.2.1.add ha.2.2.2)
  have hconst : IntegrableOn (fun _ : Vec d => (1 : ℝ)) V :=
    integrableOn_const (by rw [polynomialCube_volume_one]; norm_num)
  have hind : IntegrableOn
      ((responseCylinder epsilon).indicator (fun _ : Vec d => (1 : ℝ))) V :=
    hconst.indicator (responseCylinder_measurable epsilon)
  have hg : IntegrableOn g V := by
    dsimp [g]
    exact (integrableOn_const (by rw [polynomialCube_volume_one]; norm_num)).add
      (hind.const_mul ((d : ℝ) * (Λ + lam⁻¹)))
  have hpoint : ∀ x ∈ V, f x ≤ g x := by
    intro x hx
    by_cases htube : x ∈ responseCylinder epsilon
    · have hfield : polynomialCoefficientFamily d q t epsilon x =
          cylinderDiagonal (d := d) Λ lam := by
        change (if 0 < epsilon ∧ epsilon < 1 / 8 then
          cylinderCoefficient epsilon (polynomialParallel d q t epsilon)
            (polynomialPerpendicular d q t epsilon) else fun _ => 1) x = _
        split_ifs with h
        · simp [cylinderCoefficient, htube, Λ, lam]
        · exact (h ⟨hepsilon, hepsilon8⟩).elim
      have hinv : (cylinderDiagonal (d := d) Λ lam)⁻¹ =
          cylinderDiagonal Λ⁻¹ lam⁻¹ :=
        cylinderDiagonal_inv (ne_of_gt hΛ) (ne_of_gt hlam)
      have hcoefEntry : ∀ i : Fin d,
          (if i.val = 0 then Λ else lam) ≤ Λ := by
        intro i
        split_ifs with hi
        · exact le_rfl
        · exact hlam1.trans hΛ1
      have hinvEntry : ∀ i : Fin d,
          (if i.val = 0 then Λ⁻¹ else lam⁻¹) ≤ lam⁻¹ := by
        intro i
        split_ifs with hi
        · have hΛinv : Λ⁻¹ ≤ 1 := (inv_le_one₀ hΛ).2 hΛ1
          have hlamInv : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam).2 hlam1
          exact hΛinv.trans hlamInv
        · exact le_rfl
      have htrace : (cylinderDiagonal (d := d) Λ lam).trace ≤ (d : ℝ) * Λ :=
        polynomialDiagonal_trace_le _ _ hcoefEntry
      have hinvtrace : (cylinderDiagonal (d := d) Λ⁻¹ lam⁻¹).trace ≤
          (d : ℝ) * lam⁻¹ := polynomialDiagonal_trace_le _ _ hinvEntry
      have hindicator :
          (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x = 1 := by
        simp [Set.indicator, htube]
      change (polynomialCoefficientFamily d q t epsilon x).trace +
          ((polynomialCoefficientFamily d q t epsilon x)⁻¹).trace ≤
        2 * (d : ℝ) + (d : ℝ) * (Λ + lam⁻¹) *
          (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x
      rw [hfield, hinv, hindicator]
      linarith [htrace, hinvtrace]
    · have hfield : polynomialCoefficientFamily d q t epsilon x = 1 := by
        change (if 0 < epsilon ∧ epsilon < 1 / 8 then
          cylinderCoefficient epsilon (polynomialParallel d q t epsilon)
            (polynomialPerpendicular d q t epsilon) else fun _ => 1) x = _
        split_ifs with h
        · simp [cylinderCoefficient, htube]
        · rfl
      have hindicator :
          (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x = 0 := by
        simp [Set.indicator, htube]
      change (polynomialCoefficientFamily d q t epsilon x).trace +
          ((polynomialCoefficientFamily d q t epsilon x)⁻¹).trace ≤
        2 * (d : ℝ) + (d : ℝ) * (Λ + lam⁻¹) *
          (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x
      rw [hfield, hindicator]
      simp
      linarith
  have hmono := setIntegral_mono_on hf hg hVmeas hpoint
  have hVvol : (volume V).toReal = 1 := by
    rw [polynomialCube_volume_one]
    norm_num
  have hIind :
      (∫ x in V, (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x) =
        (volume (V ∩ responseCylinder epsilon)).toReal := by
    change (∫ x in originCube (d := d) 1,
      (responseCylinder epsilon).indicator (fun _ => (1 : ℝ)) x) =
        (volume (originCube (d := d) 1 ∩ responseCylinder epsilon)).toReal
    exact polynomialTube_indicator_integral (d := d) epsilon
  have hbox : V ∩ responseCylinder epsilon ⊆ Sharpness.lineAnnulusBox epsilon := by
    intro x hx
    exact Sharpness.mem_lineAnnulusBox hx.1 (le_of_lt (by
      simpa [responseCylinder] using hx.2))
  have hTubeVol : (volume (V ∩ responseCylinder epsilon)).toReal ≤
      2 * (4 * epsilon) ^ (d - 1) := by
    calc
      _ ≤ (volume (Sharpness.lineAnnulusBox epsilon)).toReal := by
        apply ENNReal.toReal_mono (Sharpness.lineAnnulusBox_volume_lt_top epsilon).ne
        exact measure_mono hbox
      _ = 2 * (4 * epsilon) ^ (d - 1) :=
        Sharpness.lineAnnulusBox_volume (by linarith : 0 ≤ epsilon)
  have hpowFactor : (4 * epsilon) ^ (d - 1 : ℕ) =
      4 ^ (d - 1 : ℕ) * epsilon ^ (d - 1 : ℕ) := by rw [mul_pow]
  have hcalculus :
      ∫ x in V, g x = 2 * (d : ℝ) +
        (d : ℝ) * (Λ + lam⁻¹) * (volume (V ∩ responseCylinder epsilon)).toReal := by
    dsimp [g]
    have hconstant : IntegrableOn (fun _ : Vec d => 2 * (d : ℝ)) V := by
      change Integrable (fun _ : Vec d => 2 * (d : ℝ)) (volume.restrict V)
      simpa only [mul_one] using hconst.const_mul (2 * (d : ℝ))
    rw [integral_add hconstant
      (hind.const_mul ((d : ℝ) * (Λ + lam⁻¹)))]
    rw [setIntegral_const, smul_eq_mul, measureReal_def, hVvol]
    rw [integral_const_mul ((d : ℝ) * (Λ + lam⁻¹))]
    rw [← mul_assoc, hIind]
    rw [show (d : ℝ) * (Λ + lam⁻¹) * _ =
      (d : ℝ) * (Λ + lam⁻¹) * (volume (V ∩ responseCylinder epsilon)).toReal by rfl]
    norm_num
  have hsecond : (d : ℝ) * (Λ + lam⁻¹) *
      (volume (V ∩ responseCylinder epsilon)).toReal ≤
        2 * (d : ℝ) * 4 ^ (d - 1 : ℕ) * (d : ℝ) := by
    have hAreal : Λ * epsilon ^ (d - 1 : ℕ) ≤ (d : ℝ) - 1 := by
      simpa [Λ, lam] using hAvol
    have hBreal : lam⁻¹ * epsilon ^ (d - 1 : ℕ) ≤ 1 := by
      simpa [lam] using hBvol
    have hTube := mul_le_mul_of_nonneg_left hTubeVol (by positivity : 0 ≤ (d : ℝ) * (Λ + lam⁻¹))
    rw [hpowFactor] at hTube
    have hsum : Λ * epsilon ^ (d - 1 : ℕ) +
        lam⁻¹ * epsilon ^ (d - 1 : ℕ) ≤ (d : ℝ) := by linarith
    have hprod : (Λ + lam⁻¹) * epsilon ^ (d - 1 : ℕ) ≤ (d : ℝ) := by
      rw [add_mul]
      exact hsum
    calc
      (d : ℝ) * (Λ + lam⁻¹) * (volume (V ∩ responseCylinder epsilon)).toReal ≤
          (d : ℝ) * (Λ + lam⁻¹) *
            (2 * (4 ^ (d - 1 : ℕ) * epsilon ^ (d - 1 : ℕ))) := hTube
      _ = 2 * (d : ℝ) * 4 ^ (d - 1 : ℕ) *
          ((Λ + lam⁻¹) * epsilon ^ (d - 1 : ℕ)) := by ring
      _ ≤ 2 * (d : ℝ) * 4 ^ (d - 1 : ℕ) * (d : ℝ) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
  have hbound : ∫ x in V, f x ≤ C := by
    calc
      _ ≤ ∫ x in V, g x := hmono
      _ = 2 * (d : ℝ) + (d : ℝ) * (Λ + lam⁻¹) *
          (volume (V ∩ responseCylinder epsilon)).toReal := hcalculus
      _ ≤ C := by dsimp [C]; linarith [hsecond]
  change (∫ x in V, f x) ≤ C
  exact hbound

end

end CoarseDeGiorgi.SharpnessExamples
