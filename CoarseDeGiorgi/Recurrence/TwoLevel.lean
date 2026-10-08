import CoarseDeGiorgi.Recurrence.EnergyStep
import CoarseDeGiorgi.Recurrence.Bulk
import CoarseDeGiorgi.Assembly.HybridEnergyENN
import CoarseDeGiorgi.Harnack.Moments.MomentComparison

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Recurrence

open Assembly

/-- Sum the energy and value estimates with one uniform constant and the larger radius exponent. -/
theorem combine_energy_and_mass {A B : ℝ≥0∞} {γ₁ γ₂ γ : ℝ}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hγ₁ : γ₁ ≤ γ) (hγ₂ : γ₂ ≤ γ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (δ ε k s v : ℝ) (Θ Y Δ E N : ℝ≥0∞),
      δ ≤ 1 →
      E ≤ ENNReal.ofReal ε * Y ^ (2 : ℝ) +
        A * (ENNReal.ofReal δ) ^ (-γ₁) * Θ ^ k * Y ^ s * Δ ^ (2 - s) →
      N ≤ B * (ENNReal.ofReal δ) ^ (-γ₂) * Y ^ v * Δ ^ (2 - v) →
      E + N ≤ ENNReal.ofReal ε * Y ^ (2 : ℝ) +
        C * (ENNReal.ofReal δ) ^ (-γ) *
          (Θ ^ k * Y ^ s * Δ ^ (2 - s) + Y ^ v * Δ ^ (2 - v)) := by
  refine ⟨A + B, (ENNReal.add_ne_top.mpr ⟨hA, hB⟩).lt_top, ?_⟩
  intro δ ε k s v Θ Y Δ E N hδ1 hE hN
  have hδENN : ENNReal.ofReal δ ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hδ1
  have hrad₁ : (ENNReal.ofReal δ) ^ (-γ₁) ≤ (ENNReal.ofReal δ) ^ (-γ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδENN (neg_le_neg hγ₁)
  have hrad₂ : (ENNReal.ofReal δ) ^ (-γ₂) ≤ (ENNReal.ofReal δ) ^ (-γ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδENN (neg_le_neg hγ₂)
  calc
    E + N ≤ (ENNReal.ofReal ε * Y ^ (2 : ℝ) +
        A * (ENNReal.ofReal δ) ^ (-γ₁) * Θ ^ k * Y ^ s * Δ ^ (2 - s)) +
        B * (ENNReal.ofReal δ) ^ (-γ₂) * Y ^ v * Δ ^ (2 - v) := add_le_add hE hN
    _ ≤ (ENNReal.ofReal ε * Y ^ (2 : ℝ) +
        (A + B) * (ENNReal.ofReal δ) ^ (-γ) * Θ ^ k * Y ^ s * Δ ^ (2 - s)) +
        (A + B) * (ENNReal.ofReal δ) ^ (-γ) * Y ^ v * Δ ^ (2 - v) := by
      gcongr
      · exact le_add_right le_rfl
      · exact le_add_left le_rfl
    _ = _ := by ring

/-- Proposition `p.two.level.recurrence` from Proposition `p.good.radius.energy` (the hypothesis
`h72` is `p.good.radius.energy` restricted to narrower widths) and Propositions
`p.fractional.localization` and `p.good.radius`. -/
theorem two_level_recurrence_of_energy (h72 :

    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
            MemH1a a (originCube 1) v G →
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ v x) →
            ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              eLpNorm v (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube ρ₂)) < ⊤ →
              ∀ vᵢ : ℕ → Vec d → ℝ,
                (∀ i, IsSmoothCore a (originCube 1) (vᵢ i)) →
                (∀ i, ∀ x ∈ originCube (d := d) 1, 0 ≤ vᵢ i x) →
                Filter.Tendsto
                  (fun i => h1aWeightedNorm a (originCube 1)
                    (fun x => vᵢ i x - v x)
                    (fun x => smoothGrad (vᵢ i) x - G x))
                  Filter.atTop (nhds 0) →
                ∀ τ ∈ selectionInterval ρ₁ ρ₂, ∀ ns : ℕ → ℕ, StrictMono ns →
                  ∀ C₅ : ℝ≥0∞, C₅ < ⊤ →
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N →
                    Filter.Tendsto
                      (fun i => surfaceFracNorm τ (alphaParam t) (paramR q)
                        (fun x => positiveCap (vᵢ (ns i)) k N x - positiveCap v k N x))
                      Filter.atTop (nhds 0)) →
                  sampledResponseSeries a ha s p τ ≤
                    C₅ * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / (2 * p))) *
                      (upperMoment a ha s p hs (le_of_lt hp)).rpow (1 / 2) →
                  surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ ≤
                    C₅ * (ENNReal.ofReal (ρ₂ - ρ₁))⁻¹ *
                      weightedEnergy a (originCube ρ₂) G →
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N → ∀ τ' : ℝ,
                    surfaceEnergyMaximal ρ₁ ρ₂ a ha (positiveCapGradient v G k N) τ' ≤
                      surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ') →
                  ∀ k : ℝ,
                    IsWeightedSubsolution a (originCube 1) (positiveCap v k ⊤)
                      (positiveCapGradient v G k ⊤) →
                    ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (20000 * (d : ℝ)) →
                      weightedEnergy a (originCube τ) (positiveCapGradient v G k ⊤) ≤
                        C * sampledResponseSeries a ha s p τ *
                          (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                          ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                            surfaceFracSeminorm τ (alphaParam t) (paramR q)
                              (positiveCap v k ⊤) +
                            (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                              eLpNorm (positiveCap v k ⊤) 2 (surfaceMeasure τ))) :

    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
        (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
        0 < paramTheta d p q s t →
        ∃ C : ℝ≥0∞, C < ⊤ ∧
          ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
            spatialMomentRange a ha p q s t →
            ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
              (hu : IsWeightedSubsolution a (originCube 1) u G) →
              ∀ l₀ l₁ ρ₁ ρ₂ : ℝ, 0 ≤ l₀ → l₀ < l₁ →
                (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
                twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂ < ⊤ →
                ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₁ ρ₁) 2 ≤
                  ENNReal.ofReal ε₀ *
                    ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂) 2 +
                  C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaRec d p q s t) *
                    (ENNReal.rpow (contrast a ha s t p q hs ht
                        (le_of_lt hp) (le_of_lt hq))
                        ((1 - sigmaLower d q t) / paramTheta d p q s t) *
                      ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂)
                          (rBoundaryParam (d := d) q t) *
                      ENNReal.rpow (ENNReal.ofReal (l₁ - l₀))
                          (2 - rBoundaryParam (d := d) q t) +
                    ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂)
                        (2 * rStarParam (d := d) q t / paramR q) *
                      ENNReal.rpow (ENNReal.ofReal (l₁ - l₀))
                        (2 - 2 * rStarParam (d := d) q t / paramR q)) := by
  intro ε hε hε1 d hd p q s t hp hq hs ht hθ
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Ke, hKe, henergy⟩ := energy_step_of_energy h72 d hd p q s t hp hq hs ht hθ
  obtain ⟨B, -, hB, hbulk⟩ := bulk_step d hd p q s t hp hq hs ht hθ
  obtain ⟨hα, hα1, hr, hr2, hcrit, -, hz, hstar⟩ := Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hσ0 : 0 ≤ sigmaUpper d p s := by
    unfold sigmaUpper
    have : 0 ≤ ((d : ℝ) - 1) / (2 * p) := by
      apply div_nonneg <;> linarith only [hd3, hp0]
    linarith only [hs, this]
  have hγθ : paramTheta d p q s t ≤ gammaLoc p q t := by
    unfold paramTheta gammaLoc
    have h1 : 0 ≤ (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) := by
      have : 0 ≤ (d : ℝ) - 1 := by linarith only [hd3]
      positivity
    have h2 : 0 < 1 / (2 * p) := by positivity
    have h3 : 0 < 1 / (2 * q) := by positivity
    linarith only [hs, h1, h2, h3]
  let η := 1 / (2 * p) + 1 / 2 + (alphaParam t + 1 / paramR q) * rBoundaryParam (d := d) q t / 2
  obtain ⟨A, hA, habsorb⟩ := hybrid_energy_level_absorption_enn (η := η)
    (γ := gammaLoc p q t) (m := sigmaUpper d p s) (s := rBoundaryParam (d := d) q t) hKe.ne
    (by positivity : 0 < 20000 * (d : ℝ)) hθ hγθ hσ0 hε
  have hx : 1 + sigmaUpper d p s / paramTheta d p q s t =
      (1 - sigmaLower d q t) / paramTheta d p q s t := by
    apply (eq_div_iff hθ.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hθ.ne', one_mul]
    unfold paramTheta sigmaUpper sigmaLower
    ring
  have hx0 : 0 ≤ (1 - sigmaLower d q t) / paramTheta d p q s t := by
    rw [← hx]
    have : 0 ≤ sigmaUpper d p s / paramTheta d p q s t := div_nonneg hσ0 hθ.le
    linarith only [this]
  have hexpE : 2 * η + 2 * gammaLoc p q t * sigmaUpper d p s / paramTheta d p q s t ≤
      gammaRec d p q s t := by
    unfold gammaRec
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    dsimp only [η]
    ring
  have hexpB : 2 * alphaParam t * rStarParam (d := d) q t / paramR q ≤ gammaRec d p q s t :=
    le_max_right _ _
  obtain ⟨C, hC, hcombine⟩ := combine_energy_and_mass
    (A := A * (2 : ℝ≥0∞) ^ ((1 - sigmaLower d q t) / paramTheta d p q s t)) (B := B)
    (ENNReal.mul_ne_top hA.ne (ENNReal.rpow_ne_top_of_nonneg hx0 (by norm_num))) hB.ne hexpE hexpB
  refine ⟨C, hC, ?_⟩
  intro a ha hrange u G hu l₀ l₁ ρ₁ ρ₂ hl₀ hl hρ hgap hR hY
  have huMem : MemH1a a (originCube 1) u G := hu.1
  have huM : AEStronglyMeasurable u (volume.restrict (originCube 1)) := huMem.1
  let u₀ := huM.mk u
  have heq := huM.ae_eq_mk
  have hu₀ : IsWeightedSubsolution a (originCube 1) u₀ G :=
    ⟨Weighted.MemH1a.congr_ae hu.1 heq EventuallyEq.rfl, hu.2⟩
  have hYeq := hybrid_quantity_congr_ae a ha q t ht hq.le G heq l₀ ρ₂ hR
  have hρ1 := hgap.le.trans hR
  have hYbeq := hybrid_quantity_congr_ae a ha q t ht hq.le G heq l₁ ρ₁ hρ1
  rw [hYeq, hYbeq]
  rw [hYeq] at hY
  let Y := twoLevelQuantity a ha q t ht hq.le u₀ G l₀ ρ₂
  have hYfin : Y ≠ ⊤ := hY.ne
  by_cases hY0 : Y = 0
  · have hmono : twoLevelQuantity a ha q t ht hq.le u₀ G l₁ ρ₁ ≤ Y :=
      energy_to_sup_quantity_mono (a := a) (ha := ha) q t ht hq.le u₀ G hu₀.1.1 hl.le hgap.le hR
    have hzero := le_antisymm (hmono.trans_eq hY0) bot_le
    rw [hzero]
    exact (ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).le.trans bot_le
  have hδ : 0 < ρ₂ - ρ₁ := sub_pos.mpr hgap
  have hδ1 : ρ₂ - ρ₁ ≤ 1 := by linarith only [hρ, hR]
  have hΔ : 0 < l₁ - l₀ := sub_pos.mpr hl
  have hmoms := caccioppoli_moments_finite (a := a) (ha := ha) hp hq hs ht hrange
  have hΘ1 : 1 ≤ contrast a ha s t p q hs ht hp.le hq.le :=
    Harnack.Moments.moment_contrast_ge_one (by omega) a ha hs ht hp.le hq.le hmoms.1 hmoms.2.1
  have hLowerFinite : lowerMoment a ha t q ht hq.le ^ (-1 : ℝ) ≠ ⊤ := by
    by_cases htopp : lowerMoment a ha t q ht hq.le = ⊤
    · simp only [htopp, ENNReal.rpow_neg_one, ENNReal.inv_top, ENNReal.zero_ne_top, ne_eq,
        not_false_eq_true]
    · exact ENNReal.rpow_ne_top_of_ne_zero hmoms.2.1.ne' htopp
  have hw := Selection.source_truncation_pair a ha u₀ G hu₀.1 l₁
  have hefin : weightedEnergy a (originCube ρ₁) (positiveTruncationGradient u₀ G l₁) ≠ ⊤ :=
    ((lintegral_mono_set (caccioppoli_cube_mono hρ1)).trans_lt
      (Weighted.MemH1a.energy_lt_top (hybrid_unitCube_domain (d := d)).1.isOpen ha hw)).ne
  have hE := habsorb (ρ₂ - ρ₁) (l₁ - l₀) (contrast a ha s t p q hs ht hp.le hq.le) Y
    (lowerMoment a ha t q ht hq.le ^ (-1 : ℝ) *
      weightedEnergy a (originCube ρ₁) (positiveTruncationGradient u₀ G l₁))
    hδ hδ1 hΔ hmoms.2.2.ne hYfin hY0 (ENNReal.mul_ne_top hLowerFinite hefin)
    (henergy a ha hrange u₀ G hu₀ huM.measurable_mk l₀ l₁ ρ₁ ρ₂ hl hρ hgap hR hYfin)
  have hN := hbulk a ha hrange u₀ G hu₀.1 huM.measurable_mk l₀ l₁ ρ₁ ρ₂ hl hρ hgap hR
  rw [hx] at hE
  have h1 : (1 + contrast a ha s t p q hs ht hp.le hq.le) ^ ((1 - sigmaLower d q t) / paramTheta d p q s t) ≤
      (2 : ℝ≥0∞) ^ ((1 - sigmaLower d q t) / paramTheta d p q s t) *
        contrast a ha s t p q hs ht hp.le hq.le ^ ((1 - sigmaLower d q t) / paramTheta d p q s t) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hx0]
    apply ENNReal.rpow_le_rpow _ hx0
    rw [two_mul]
    exact add_le_add_left hΘ1 _
  have hE' : lowerMoment a ha t q ht hq.le ^ (-1 : ℝ) *
        weightedEnergy a (originCube ρ₁) (positiveTruncationGradient u₀ G l₁) ≤
      ENNReal.ofReal ε * Y ^ (2 : ℝ) +
        (A * (2 : ℝ≥0∞) ^ ((1 - sigmaLower d q t) / paramTheta d p q s t)) *
          ENNReal.ofReal (ρ₂ - ρ₁) ^ (-(2 * η + 2 * gammaLoc p q t * sigmaUpper d p s /
            paramTheta d p q s t)) *
          contrast a ha s t p q hs ht hp.le hq.le ^ ((1 - sigmaLower d q t) / paramTheta d p q s t) *
          Y ^ rBoundaryParam (d := d) q t *
          ENNReal.ofReal (l₁ - l₀) ^ (2 - rBoundaryParam (d := d) q t) := by
    refine hE.trans (add_le_add_right ?_ _)
    calc _ = A * ENNReal.ofReal (ρ₂ - ρ₁) ^ (-(2 * η + 2 * gammaLoc p q t * sigmaUpper d p s /
            paramTheta d p q s t)) * (1 + contrast a ha s t p q hs ht hp.le hq.le) ^
              ((1 - sigmaLower d q t) / paramTheta d p q s t) *
            (Y ^ rBoundaryParam (d := d) q t *
              ENNReal.ofReal (l₁ - l₀) ^ (2 - rBoundaryParam (d := d) q t)) := by ring
      _ ≤ A * ENNReal.ofReal (ρ₂ - ρ₁) ^ (-(2 * η + 2 * gammaLoc p q t * sigmaUpper d p s /
            paramTheta d p q s t)) * ((2 : ℝ≥0∞) ^ ((1 - sigmaLower d q t) / paramTheta d p q s t) *
              contrast a ha s t p q hs ht hp.le hq.le ^ ((1 - sigmaLower d q t) / paramTheta d p q s t)) *
            (Y ^ rBoundaryParam (d := d) q t *
              ENNReal.ofReal (l₁ - l₀) ^ (2 - rBoundaryParam (d := d) q t)) := by gcongr
      _ = _ := by ring
  have hsum := hcombine (ρ₂ - ρ₁) ε ((1 - sigmaLower d q t) / paramTheta d p q s t)
    (rBoundaryParam (d := d) q t) (2 * rStarParam (d := d) q t / paramR q)
    (contrast a ha s t p q hs ht hp.le hq.le) Y (ENNReal.ofReal (l₁ - l₀)) _ _ hδ1 hE' hN
  exact (hybrid_quantity_sq a ha q t ht hq.le u₀ G l₁ ρ₁).le.trans
    ((add_comm _ _).le.trans hsum)

end CoarseDeGiorgi.Recurrence
