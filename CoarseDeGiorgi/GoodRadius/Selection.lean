module

public import CoarseDeGiorgi.Statements.LowerFractionalBound
public import CoarseDeGiorgi.Harnack.Selection.Radius
public import CoarseDeGiorgi.Harnack.Selection.CoareaLr
public import CoarseDeGiorgi.Selection.SourceConstants
public import CoarseDeGiorgi.Selection.SourceResponses
public import CoarseDeGiorgi.Selection.SourceRepresentatives
public import CoarseDeGiorgi.Assembly.HybridFractional
public import CoarseDeGiorgi.Assembly.HybridParameters
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.ParamR

/-!
# Step 2 of Proposition `p.good.radius`: excluding the bad radii

Chebyshev (via `exists_uniform_four_slot_surface_constant`) on the interval of radii. The
fractional bound is fed by the localization bound of Proposition `p.fractional.localization`
(exponent `δ^{-α}`), supplied through the bound on `fracNorm univ F` for a measurable function `F`
agreeing with `w₀` on almost every selected surface.
-/

@[expose] public section

namespace CoarseDeGiorgi.GoodRadius

open Homogenization MeasureTheory Set Filter CoarseDeGiorgi.Selection
  CoarseDeGiorgi.Harnack.Selection
open scoped ENNReal
noncomputable section

theorem selection_bounds :
    ∀ n : ℕ, 3 ≤ n + 1 → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta (n + 1) p q s t → ∀ Cl : ℝ≥0∞, Cl < ⊤ →
      ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧
        ∀ (a : CoeffField (n + 1)) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (w₀ F : Vec (n + 1) → ℝ) (G : Vec (n + 1) → Vec (n + 1)),
            MemH1a a (originCube 1) w₀ G → Measurable w₀ → Measurable F →
            ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
            (∀ᵐ τ ∂volume.restrict (selectionInterval ρ R),
              F =ᵐ[surfaceMeasure τ] w₀) →
            fracNorm univ (alphaParam t) (paramR q) F ≤
              Cl * (ENNReal.ofReal (R - ρ)).rpow (-alphaParam t) *
                ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
                    (weightedEnergy a (originCube R) G).rpow (1 / 2) +
                  eLpNorm w₀ (ENNReal.ofReal (paramR q))
                    (volume.restrict (originCube R))) →
            ∀ Good : ℝ → Prop,
              (∀ᵐ τ ∂volume.restrict (selectionInterval ρ R), Good τ) →
              ∃ τ ∈ selectionInterval ρ R, Good τ ∧
                sourceSampledSeries a ha s p τ ≤
                  C * ENNReal.ofReal ((R - ρ) ^ (-(1 / (2 * p)))) *
                    (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) ∧
                surfaceEnergyMaximal ρ R
                    (fun x => ENNReal.ofReal
                      (vecDot (G x) (matVecMul (a x) (G x)))) τ ≤
                  C * ENNReal.ofReal ((R - ρ) ^ (-1 : ℝ)) *
                    weightedEnergy a (originCube R) G ∧
                surfaceFracNorm τ (alphaParam t) (paramR q) w₀ ≤
                  C * (ENNReal.ofReal (R - ρ)).rpow (-alphaParam t - 1 / paramR q) *
                    ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
                        (weightedEnergy a (originCube R) G).rpow (1 / 2) +
                      eLpNorm w₀ (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube R))) ∧
                eLpNorm w₀ (ENNReal.ofReal (paramR q))
                    (surfaceMeasure τ) ≤
                  C * ENNReal.ofReal ((R - ρ) ^ (-(1 / paramR q))) *
                    eLpNorm w₀ (ENNReal.ofReal (paramR q))
                      (volume.restrict (originCube R)) ∧
                eLpNorm w₀ 2 (surfaceMeasure τ) ≤
                  C * ENNReal.ofReal ((R - ρ) ^ (-(1 / 2 : ℝ))) *
                    eLpNorm w₀ 2 (volume.restrict (originCube R)) := by
  intro n hd p q s t hp hq hs ht hθ Cl hCl
  obtain ⟨hα, hα1, hr, _, _, _, _, _⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  change 0 < alphaParam t at hα
  change alphaParam t < 1 at hα1
  change 1 < paramR q at hr
  obtain ⟨T, _, hselect⟩ := exists_uniform_four_slot_surface_constant
    (n := n) hα hα1 hr
  let N := ENNReal.ofReal (1 - Real.rpow 3 (-s))
  have hN : 0 < N := ENNReal.ofReal_pos.mpr
    (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3) (neg_neg_of_pos hs)))
  let Aresp : ℝ≥0∞ := ENNReal.ofReal (32 : ℝ) ^ (1 / (2 * p)) *
    (ENNReal.ofReal (2 + 400 * ((n + 1 : ℕ) : ℝ)) *
      (Nat.factorial (n + 1) : ℝ≥0∞)) ^ (1 / (2 * p)) / N
  let Afrac : ℝ≥0∞ := ENNReal.ofReal (32 : ℝ) ^ (1 / paramR q) *
    ENNReal.ofReal T ^ (1 / paramR q) * Cl
  let ALr : ℝ≥0∞ := ENNReal.ofReal (32 : ℝ) ^ (1 / paramR q) *
    (2 : ℝ≥0∞) ^ (1 / paramR q)
  let AL2 : ℝ≥0∞ := ENNReal.ofReal (32 : ℝ) ^ (1 / 2 : ℝ) *
    (2 : ℝ≥0∞) ^ (1 / 2 : ℝ)
  let C := max Aresp (max Afrac (max ALr (max AL2 192))) + 1
  have hfac : ENNReal.ofReal (2 + 400 * ((n + 1 : ℕ) : ℝ)) *
      (Nat.factorial (n + 1) : ℝ≥0∞) < ⊤ := by finiteness
  have hfacpow : (ENNReal.ofReal (2 + 400 * ((n + 1 : ℕ) : ℝ)) *
      (Nat.factorial (n + 1) : ℝ≥0∞)) ^ (1 / (2 * p)) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hfac.ne
  have hnumerator : ENNReal.ofReal (32 : ℝ) ^ (1 / (2 * p)) *
      (ENNReal.ofReal (2 + 400 * ((n + 1 : ℕ) : ℝ)) *
        (Nat.factorial (n + 1) : ℝ≥0∞)) ^ (1 / (2 * p)) < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      hfacpow
  have hAr : Aresp ≠ ⊤ := (ENNReal.div_lt_top hnumerator.ne hN.ne').ne
  have hAf : Afrac ≠ ⊤ := by dsimp [Afrac]; finiteness
  have hAlr : ALr ≠ ⊤ := by
    dsimp [ALr]
    have h32 : (ENNReal.ofReal (32 : ℝ)) ^ (1 / paramR q) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have h2 : (2 : ℝ≥0∞) ^ (1 / paramR q) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)
    exact (ENNReal.mul_lt_top h32 h2).ne
  have hAl2 : AL2 ≠ ⊤ := by
    dsimp [AL2]
    have h32 : (ENNReal.ofReal (32 : ℝ)) ^ (1 / 2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have h2 : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num)
    exact (ENNReal.mul_lt_top h32 h2).ne
  have hC : C < ⊤ := by dsimp [C]; finiteness
  have hCr : Aresp ≤ C := (le_max_left _ _).trans le_self_add
  have hCf : Afrac ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans le_self_add)
  have hClr : ALr ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans le_self_add))
  have hCl2 : AL2 ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans le_self_add)))
  have hCe : (192 : ℝ≥0∞) ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans le_self_add)))
  refine ⟨C, lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 192) hCe, hC, ?_⟩
  intro a ha hrange w₀ F G hw₀m hw₀ hF ρ R hρ hgap hR hFeq hFb Good hGood
  have hρ0 : 0 ≤ ρ := by linarith only [hρ]
  have hδ : 0 < R - ρ := sub_pos.mpr hgap
  have hAnnR : cubicalAnnulus (n + 1) ρ R ⊆ originCube R := by
    intro x hx i
    have hi : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact abs_lt.mp (by linarith only [hi, hx.2])
  have hAnn1 := hAnnR.trans (Assembly.caccioppoli_cube_mono hR)
  have hEm := (Weighted.quadratic_aestronglyMeasurable ha hw₀m.2.1).aemeasurable.ennreal_ofReal
  let g := hEm.mk (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))))
  have hg : Measurable g := hEm.measurable_mk
  have hge := ae_restrict_of_ae_restrict_of_subset hAnn1 hEm.ae_eq_mk.symm
  have hE : (∫⁻ x in cubicalAnnulus (n + 1) ρ R, g x) ≤
      weightedEnergy a (originCube R) G := by
    rw [lintegral_congr_ae hge]
    exact lintegral_mono_set hAnnR
  have hEfin : weightedEnergy a (originCube R) G ≠ ⊤ :=
    ((lintegral_mono_set (Assembly.caccioppoli_cube_mono hR)).trans_lt
      (Weighted.MemH1a.energy_lt_top
        (Assembly.hybrid_unitCube_domain (d := n + 1)).1.isOpen ha hw₀m)).ne
  obtain ⟨τ, hτ, hgood', hS, hfrac, hLr, hL2, hmax⟩ := hselect
    ρ R p hρ hR hgap hp.le F w₀ w₀ _ _ _ g
    (sourceSampledSeries a ha s p) Good
    hF hw₀ hw₀ hg (source_sampled_series_measurable a ha s p) hFeq
    hFb hEfin hE
    (source_response_sampling a ha hs hp.le) hGood
  refine ⟨τ, hτ, hgood', ?_, ?_, ?_, ?_, ?_⟩
  · apply hS.trans
    rw [source_selection_gap_factor hδ]
    have he : ENNReal.ofReal (32 : ℝ) ^ (1 / (2 * p)) *
        ENNReal.ofReal ((R - ρ) ^ (-(1 / (2 * p)))) *
        ((ENNReal.ofReal (2 + 400 * ((n + 1 : ℕ) : ℝ)) *
          (Nat.factorial (n + 1) : ℝ≥0∞)) ^ (1 / (2 * p)) *
          (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) / N) =
        Aresp * ENNReal.ofReal ((R - ρ) ^ (-(1 / (2 * p)))) *
          (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) := by
      dsimp only [Aresp]
      simp only [div_eq_mul_inv]
      ac_rfl
    change _ ≤ _
    rw [he]
    gcongr
  · rw [← source_surfaceEnergyMaximal_congr_ae hρ0 hge]
    apply hmax.trans
    have he : (ENNReal.ofReal (R - ρ))⁻¹ =
        ENNReal.ofReal ((R - ρ) ^ (-1 : ℝ)) := by
      rw [Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos hδ]
    rw [he]
    gcongr
  · apply hfrac.trans
    rw [source_selection_gap_factor hδ]
    have hpow : ENNReal.ofReal ((R - ρ) ^ (-(1 / paramR q))) *
        (ENNReal.ofReal (R - ρ)) ^ (-alphaParam t) =
        (ENNReal.ofReal (R - ρ)) ^ (-alphaParam t - 1 / paramR q) := by
      rw [← ENNReal.ofReal_rpow_of_pos hδ (x := R - ρ) (p := -(1 / paramR q)),
        ← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hδ).ne' ENNReal.ofReal_ne_top]
      congr 1
      ring
    have he : ENNReal.ofReal (32 : ℝ) ^ (1 / paramR q) *
        ENNReal.ofReal ((R - ρ) ^ (-(1 / paramR q))) *
        ENNReal.ofReal T ^ (1 / paramR q) *
        (Cl * (ENNReal.ofReal (R - ρ)).rpow (-alphaParam t) *
          ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
            (weightedEnergy a (originCube R) G).rpow (1 / 2) +
            eLpNorm w₀ (ENNReal.ofReal (paramR q))
              (volume.restrict (originCube R)))) =
        Afrac * (ENNReal.ofReal ((R - ρ) ^ (-(1 / paramR q))) *
          (ENNReal.ofReal (R - ρ)).rpow (-alphaParam t)) *
          ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
            (weightedEnergy a (originCube R) G).rpow (1 / 2) +
            eLpNorm w₀ (ENNReal.ofReal (paramR q))
              (volume.restrict (originCube R))) := by
      dsimp only [Afrac]
      ac_rfl
    simp only [ENNReal.rpow_eq_pow] at he ⊢
    rw [he, hpow]
    gcongr
  · have hLr' := hLr
    apply hLr'.trans
    rw [source_selection_gap_factor hδ]
    calc
      _ = ALr * ENNReal.ofReal ((R - ρ) ^ (-(1 / paramR q))) *
          eLpNorm w₀ (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) := by
        dsimp only [ALr]
        ac_rfl
      _ ≤ C * ENNReal.ofReal ((R - ρ) ^ (-(1 / paramR q))) *
          eLpNorm w₀ (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) := by
        gcongr
  · have hL2' := hL2
    apply hL2'.trans
    rw [source_selection_gap_factor hδ]
    calc
      _ = AL2 * ENNReal.ofReal ((R - ρ) ^ (-(1 / 2 : ℝ))) *
          eLpNorm w₀ 2 (volume.restrict (originCube R)) := by
        dsimp only [AL2]
        ac_rfl
      _ ≤ C * ENNReal.ofReal ((R - ρ) ^ (-(1 / 2 : ℝ))) *
          eLpNorm w₀ 2 (volume.restrict (originCube R)) := by
        gcongr

end
end CoarseDeGiorgi.GoodRadius
