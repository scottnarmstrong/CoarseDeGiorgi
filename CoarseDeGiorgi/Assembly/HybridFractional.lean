module

public import CoarseDeGiorgi.Assembly.HybridDensity
public import CoarseDeGiorgi.Assembly.HybridRadius
public import CoarseDeGiorgi.Assembly.HybridLocalNorm
public import CoarseDeGiorgi.Assembly.HybridParameters
public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import CoarseDeGiorgi.LowerFractional.Restriction

@[expose] public section

namespace CoarseDeGiorgi.Assembly
open Homogenization MeasureTheory Set CoarseDeGiorgi.Localization
open scoped ENNReal

theorem hybrid_radiusCube_eq_originCube {d : ℕ} (R : ℝ) :
    radiusCube (d := d) R = CoarseDeGiorgi.originCube R := by
  ext x
  simp only [radiusCube, CoarseDeGiorgi.originCube, mem_ofPred_eq, abs_lt]

theorem hybrid_unitCube_domain {d : ℕ} :
    IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1) ∧ (CoarseDeGiorgi.originCube (d := d) 1).Nonempty := by
  have he : CoarseDeGiorgi.originCube (d := d) 1 = auxCube 1 (fun _ => 0) := by
    ext x
    simp only [CoarseDeGiorgi.originCube, auxCube, sub_self, sub_zero, zpow_zero,
      Int.cast_zero, zero_mul, abs_lt]
  rw [he]
  exact ⟨LowerFractional.auxCube_isOpenBoundedConvexDomain _ _,
    LowerFractional.auxCube_nonempty _ _⟩

/-- The exact lower-fractional input supplies both inner and annular compact
localizations. Local Lʳ finiteness and every per-cube premise are discharged here. -/
theorem hybrid_fractional_localization_of_lower_fractional (h_lower_fractional :
    ∀ d : ℕ, 3 ≤ d → ∀ q t : ℝ, (hq : 1 < q) → (ht : 0 < t) →
      ∃ C : ℝ, 0 < C ∧
        ∀ p s : ℝ, (hp : 1 < p) → (hs : 0 < s) →
          ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a) →
            spatialMomentRange a ha p q s t →
            ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (G : Vec d → Vec d),
              closure (auxCube m z) ⊆ CoarseDeGiorgi.originCube 1 → MemH1a a (auxCube m z) w G →
              fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
                ENNReal.ofReal C *
                  ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2) *
                  ENNReal.rpow (weightedEnergy a (auxCube m z) G) (1 / 2)) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ B : ℝ≥0∞, 0 < B ∧ B < ⊤ ∧
        ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a) →
          spatialMomentRange a ha p q s t →
        ∀ (w : Vec d → ℝ) (G : Vec d → Vec d), MemH1a a (CoarseDeGiorgi.originCube 1) w G →
          Measurable w → ∀ g : Vec d → ℝ≥0∞, Measurable g →
          g =ᵐ[volume.restrict (CoarseDeGiorgi.originCube 1)]
            (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) →
        ∀ (δ R : ℝ) (m : ℤ) (K : Set (Vec d)) (b : ℝ),
          0 < δ → δ ≤ 1 → R ≤ 1 → gridSpacing m ≤ 1 → δ / 192 < gridSpacing m →
          LocalizationCover m K R δ →
          (∀ y ∈ K, ∀ i, |y i| ≤ b / 2) → b + 4 * gridSpacing m < R →
          fracNorm univ (alphaParam t) (paramR q) (localizedFunction m (coverIndices m K) w) ≤
            B * ENNReal.ofReal (δ ^ (-gammaOneParam (d := d) q t)) *
              ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
                  weightedEnergy a (CoarseDeGiorgi.originCube R) G ^ (1 / 2 : ℝ) +
                eLpNorm w (ENNReal.ofReal (paramR q)) (volume.restrict (CoarseDeGiorgi.originCube R))) := by
  intro d hd p q s t hp hq hs ht hθ
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hα, hα1, hr, hr2, _, _, _, _⟩ := Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hr0 : 0 < paramR q := zero_lt_one.trans hr
  obtain ⟨A, hA, h_lower⟩ := h_lower_fractional d hd q t hq ht
  obtain ⟨C, hC, hC0, hloc⟩ := hybrid_localization_rpow_of_density (d := d) hα hα1 hr hr2
  obtain ⟨hαγ, hcγ⟩ := Hybrid.localization_exponent_bounds (d := d) (t := t) hq
  obtain ⟨B, hB0, hB, hrad⟩ := hybrid_localization_radius_bound (d := d) hC hC0 hr0 hr2 hαγ hcγ
  let M : ℝ≥0∞ := ENNReal.ofReal (max A 1)
  have hM0 : 0 < M := ENNReal.ofReal_pos.mpr (hA.trans_le (le_max_left _ _))
  have hM : M ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨B * M, ENNReal.mul_pos hB0.ne' hM0.ne', ENNReal.mul_lt_top hB hM.lt_top, ?_⟩
  intro a ha hrange w G hw hwm g hg hdensity δ R m K b hδ hδ1 hR hs1 hgap hcover hK hm
  have hunit := hybrid_unitCube_domain (d := d)
  have henergy := Weighted.MemH1a.energy_lt_top hunit.1.isOpen ha hw
  have hlower0 := (caccioppoli_moments_finite (a := a) (ha := ha) hp hq hs ht hrange).2.1
  let ell := (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ)
  have hell : ell ≠ ⊤ := by
    by_cases htop : lowerMoment a ha t q ht hq.le = ⊤
    · simp only [ell, htop, ENNReal.top_rpow_of_neg (by norm_num : (-1 / 2 : ℝ) < 0), ne_eq,
        ENNReal.zero_ne_top, not_false_eq_true]
    · exact ENNReal.rpow_ne_top_of_ne_zero hlower0.ne' htop
  have hsubR : radiusCube (d := d) R ⊆ CoarseDeGiorgi.originCube 1 := by
    rw [hybrid_radiusCube_eq_originCube]
    exact caccioppoli_cube_mono hR
  have hQ (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) : closure (auxCube m z) ⊆ CoarseDeGiorgi.originCube 1 :=
    ((hcover.1 z hz).2).trans hsubR
  have hlocal (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) :
      fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
        (ENNReal.ofReal A * ell) * weightedEnergy a (auxCube m z) G ^ (1 / 2 : ℝ) :=
    h_lower p s hp hs a ha hrange m z w G (hQ z hz)
      (LowerFractional.memH1a_restrict hunit.1 hunit.2 ha
        (LowerFractional.auxCube_isOpenBoundedConvexDomain m z)
        (subset_closure.trans (hQ z hz)) hw)
  have hfin (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) :
      fracNorm (auxCube m z) (alphaParam t) (paramR q) w < ⊤ :=
    hybrid_auxiliary_norm_finite_of_energy_bound hr.le hα.le m z
      hwm.aestronglyMeasurable (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hell)
      ((lintegral_mono_set (subset_closure.trans (hQ z hz))).trans_lt henergy).ne (hlocal z hz)
  have hpow := hloc δ hδ m hs1 hgap K b R hK hm (ENNReal.ofReal A * ell) a G w hwm g hg
    (ae_restrict_of_ae_restrict_of_subset hsubR hdensity) hfin hlocal
  let E := ell * weightedEnergy a (CoarseDeGiorgi.originCube R) G ^ (1 / 2 : ℝ)
  let N := eLpNorm w (ENNReal.ofReal (paramR q)) (volume.restrict (CoarseDeGiorgi.originCube R))
  have hAM : ENNReal.ofReal A ≤ M := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hM1 : 1 ≤ M := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (le_max_right A 1)
  have hL : (ENNReal.ofReal A * ell) * weightedEnergy a (radiusCube R) G ^ (1 / 2 : ℝ) ≤ M * (E + N) := by
    rw [hybrid_radiusCube_eq_originCube, mul_assoc]
    exact (mul_le_mul_left hAM E).trans (mul_le_mul_right (le_add_right le_rfl) M)
  have hN : eLpNorm w (ENNReal.ofReal (paramR q)) (volume.restrict (radiusCube R)) ≤ M * (E + N) := by
    rw [hybrid_radiusCube_eq_originCube]
    exact (le_mul_of_one_le_left' hM1).trans (mul_le_mul_right (le_add_left le_rfl) M)
  change fracNorm univ (alphaParam t) (paramR q) (localizedFunction m (coverIndices m K) w) ^ paramR q ≤
    C * ((coverIndices m K).card : ℝ≥0∞) ^ (1 - paramR q / 2) *
      ((4 ^ d : ℕ) : ℝ≥0∞) ^ (paramR q / 2) *
      ((ENNReal.ofReal A * ell) * weightedEnergy a (radiusCube R) G ^ (1 / 2 : ℝ)) ^ paramR q +
    C * ENNReal.ofReal (δ ^ (-alphaParam t * paramR q)) * ((4 ^ d : ℕ) : ℝ≥0∞) *
      eLpNorm w (ENNReal.ofReal (paramR q)) (volume.restrict (radiusCube R)) ^ paramR q at hpow
  change ∀ (δ : ℝ) (n : ℕ) (L N F Y : ℝ≥0∞),
    0 < δ → δ ≤ 1 → (n : ℝ) ≤ (960 : ℝ) ^ d * δ ^ (-(d : ℝ)) →
    L ≤ Y → N ≤ Y →
    F ^ paramR q ≤ C * (n : ℝ≥0∞) ^ (1 - paramR q / 2) *
        ((4 ^ d : ℕ) : ℝ≥0∞) ^ (paramR q / 2) * L ^ paramR q +
      C * ENNReal.ofReal (δ ^ (-alphaParam t * paramR q)) * ((4 ^ d : ℕ) : ℝ≥0∞) * N ^ paramR q →
    F ≤ B * ENNReal.ofReal (δ ^ (-gammaOneParam (d := d) q t)) * Y at hrad
  have h := hrad δ (coverIndices m K).card _ _ _ (M * (E + N)) hδ hδ1 hcover.2.1 hL hN hpow
  simpa only [mul_assoc, mul_comm, mul_left_comm, E, N, ell] using h

end CoarseDeGiorgi.Assembly
