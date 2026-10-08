module

public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.SobolevNorm
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Uniqueness and characterization of the weak derivative arrays. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi.NegSobolev

theorem isOpen_originCube {d : ℕ} (ρ : ℝ) : IsOpen (originCube (d := d) ρ) := by
  have hset : originCube (d := d) ρ =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-(ρ / 2)) (ρ / 2)) := by
    ext x
    simp [originCube, Set.mem_pi]
  rw [hset]
  exact isOpen_set_pi Set.finite_univ (by intro i hi; exact isOpen_Ioo)

theorem isWeakDerivArray_ae_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {j : ℕ}
    {w : Vec d → ℝ} {D D' : (Fin j → Fin d) → Vec d → ℝ}
    (hD : IsWeakDerivArray U j w D) (hD' : IsWeakDerivArray U j w D')
    (ι : Fin j → Fin d) : D ι =ᵐ[volume.restrict U] D' ι := by
  have hzero := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hD.2 ι).1.sub (hD'.2 ι).1) (fun φ hφ hc hs => ?_)
  · change ∀ᵐ x ∂volume.restrict U, D ι x = D' ι x
    rw [ae_restrict_iff' hU.measurableSet]
    filter_upwards [hzero] with x hx hxu
    exact sub_eq_zero.mp (hx hxu)
  · have hi : ∫ x in U, D ι x * φ x ∂volume = ∫ x in U, D' ι x * φ x ∂volume := by
      apply mul_left_cancel₀ (pow_ne_zero j (by norm_num : (-1 : ℝ) ≠ 0))
      exact ((hD.2 ι).2 φ hφ hc hs).symm.trans ((hD'.2 ι).2 φ hφ hc hs)
    have hiProd (F : Vec d → ℝ) (hF : LocallyIntegrableOn F U volume) :
        Integrable (fun x => φ x * F x) volume := by
      apply (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).mp
      · exact (hF.integrableOn_compact_subset hs hc).continuousOn_mul
          hφ.continuous.continuousOn hc
      · intro x hx
        apply subset_tsupport φ
        contrapose! hx
        apply Function.notMem_support.mpr
        rw [Function.notMem_support.mp hx, zero_mul]
    have hiD := (hiProd (D ι) (hD.2 ι).1).integrableOn (s := U)
    have hiD' := (hiProd (D' ι) (hD'.2 ι).1).integrableOn (s := U)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => ?_)]
    · simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
      rw [integral_sub hiD hiD']
      simpa only [mul_comm, sub_eq_zero] using hi
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      simp only [hφx, zero_smul]

lemma arrayFracSeminorm_congr_ae {d : ℕ} {ι : Type*} [Fintype ι]
    {U : Set (Vec d)} {α r : ℝ} {F G : ι → Vec d → ℝ}
    (h : ∀ i, F i =ᵐ[volume.restrict U] G i) :
    arrayFracSeminorm U α r F = arrayFracSeminorm U α r G := by
  have ha : ∀ᵐ x ∂volume.restrict U, ∀ i, F i x = G i x := ae_all_iff.mpr h
  unfold arrayFracSeminorm
  congr 1
  apply lintegral_congr_ae
  have hx := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict U)
    (ν := volume.restrict U)).ae ha
  have hy := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict U)
    (ν := volume.restrict U)).ae ha
  filter_upwards [hx, hy] with p hp hq
  simp only [hp, hq]

theorem sobolevNorm_eq_of_isWeakDerivArray {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {β ξ : ℝ} (hβ : 0 ≤ β) (hξ : 1 ≤ ξ) {w : Vec d → ℝ}
    (D : (j : Fin (⌊β⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ)
    (hD : ∀ j : Fin (⌊β⌋₊ + 1), IsWeakDerivArray U j w (D j)) :
    sobolevNorm U hU β ξ hβ hξ w =
      ((∑ j : Fin (⌊β⌋₊ + 1),
          ENNReal.rpow (eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal ξ)
            (volume.restrict U)) ξ) +
        (if β - ⌊β⌋₊ = 0 then 0
          else ENNReal.rpow (arrayFracSeminorm U (β - ⌊β⌋₊) ξ (D (Fin.last ⌊β⌋₊))) ξ)).rpow (1 / ξ) := by
  unfold sobolevNorm
  apply le_antisymm
  · exact iInf_le_of_le D (iInf_le_of_le hD le_rfl)
  · apply le_iInf
    intro E
    apply le_iInf
    intro hE
    have hL (j : Fin (⌊β⌋₊ + 1)) :
        eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal ξ)
          (volume.restrict U) =
        eLpNorm (fun x => Real.sqrt (∑ ι, E j ι x ^ 2)) (ENNReal.ofReal ξ)
          (volume.restrict U) := by
      apply eLpNorm_congr_ae
      have ha := ae_all_iff.mpr (fun ι => isWeakDerivArray_ae_eq hU (hD j) (hE j) ι)
      filter_upwards [ha] with x hx
      simp only [hx]
    have hS := arrayFracSeminorm_congr_ae (α := β - ⌊β⌋₊) (r := ξ)
      (fun ι => isWeakDerivArray_ae_eq hU (hD (Fin.last ⌊β⌋₊))
        (hE (Fin.last ⌊β⌋₊)) ι)
    simp only [hL, hS, le_refl]

lemma isWeakDerivArray_zero_self {d : ℕ} {U : Set (Vec d)} {w : Vec d → ℝ}
    (hw : LocallyIntegrableOn w U volume) :
    IsWeakDerivArray U 0 w (fun _ => w) := by
  refine ⟨hw, fun ι => ⟨hw, fun φ _ _ _ => ?_⟩⟩
  simp only [iteratedFDeriv_zero_apply, pow_zero, one_mul]

theorem sobolevNorm_zero {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {ξ : ℝ} (hξ : 1 ≤ ξ)
    (w : Vec d → ℝ) :
    sobolevNorm U hU 0 ξ le_rfl hξ w = eLpNorm w (ENNReal.ofReal ξ) (volume.restrict U) := by
  have hξ0 : ξ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hξ)
  by_cases hw : LocallyIntegrableOn w U volume
  · have hD : ∀ j : Fin (⌊(0 : ℝ)⌋₊ + 1),
        IsWeakDerivArray U j w (fun _ => w) := by
      rw [Nat.floor_zero]
      intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      exact isWeakDerivArray_zero_self hw
    rw [sobolevNorm_eq_of_isWeakDerivArray hU le_rfl hξ (fun _ _ => w) hD]
    rw [Nat.floor_zero]
    simp only [Nat.cast_zero, sub_zero, ite_true]
    change ((∑ j : Fin 1,
      ENNReal.rpow (eLpNorm (fun x => Real.sqrt (∑ _ : Fin j → Fin d, w x ^ 2))
        (ENNReal.ofReal ξ) (volume.restrict U)) ξ) + 0).rpow (1 / ξ) = _
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, Fintype.sum_unique, Real.sqrt_sq_eq_abs, add_zero]
    simp_rw [← Real.norm_eq_abs]
    rw [eLpNorm_norm w hw.aestronglyMeasurable]
    simpa only [one_div, ENNReal.rpow_eq_pow] using ENNReal.rpow_rpow_inv hξ0 (eLpNorm w (ENNReal.ofReal ξ)
      (volume.restrict U))
  · have htop : eLpNorm w (ENNReal.ofReal ξ) (volume.restrict U) = ⊤ := by
      by_contra hn
      have hm : MemLp w (ENNReal.ofReal ξ) (volume.restrict U) :=
        lt_top_iff_ne_top.mpr hn
      exact hw (locallyIntegrableOn_of_locallyIntegrable_restrict
        (hm.locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hξ)))
    rw [htop]
    unfold sobolevNorm
    apply top_unique
    apply le_iInf
    intro D
    apply le_iInf
    intro hD
    exact (hw (hD ⟨0, by simp⟩).1).elim

end CoarseDeGiorgi.NegSobolev
