import CoarseDeGiorgi.Recurrence.Params
import CoarseDeGiorgi.Assembly.HybridInner
import CoarseDeGiorgi.Assembly.HybridParameters
import CoarseDeGiorgi.Assembly.HybridQuantity
import CoarseDeGiorgi.Assembly.EnergyToSupQuantity
import CoarseDeGiorgi.Assembly.HybridEmbedding
import CoarseDeGiorgi.Assembly.HybridBulkQuantity
import CoarseDeGiorgi.Selection.SourceTraces
import CoarseDeGiorgi.Statements.FractionalLocalization
import CoarseDeGiorgi.Statements.DnpvTheorem6_5
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.TwoLevelQuantity

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Recurrence

open Assembly

theorem hasCompactSupport_finset_sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Vec d → ℝ)
    (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
  | insert j s hj ih =>
    have h1 : HasCompactSupport (f j) := h j (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert hj]
    exact h1.add h2

/-- Step 3 of Proposition `p.two.level.recurrence`: the `L^r` norm of the truncation at the level
`l₁` on the inner cube, from the inner fractional localization (Proposition
`p.fractional.localization`) and the critical Sobolev embedding. -/
theorem bulk_step :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ B : ℝ≥0∞, 0 < B ∧ B < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            MemH1a a (originCube 1) u G → Measurable u →
            ∀ l₀ l₁ ρ R : ℝ, l₀ < l₁ → 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
              eLpNorm (fun x => max (u x - l₁) 0) (ENNReal.ofReal (paramR q))
                  (volume.restrict (originCube ρ)) ^ (2 : ℝ) ≤
                B * ENNReal.ofReal (R - ρ) ^
                    (-(2 * alphaParam t * rStarParam (d := d) q t / paramR q)) *
                  twoLevelQuantity a ha q t ht hq.le u G l₀ R ^
                      (2 * rStarParam (d := d) q t / paramR q) *
                  ENNReal.ofReal (l₁ - l₀) ^ (2 - 2 * rStarParam (d := d) q t / paramR q) := by
  intro d hd p q s t hp hq hs ht hθ
  have : NeZero d := ⟨by omega⟩
  obtain ⟨S, φ, S', φ', hcover, hmain⟩ := fractional_localization d hd
  obtain ⟨C3, hC3, hloc⟩ := hmain p q s t hp hq hs ht hθ
  obtain ⟨hα, hα1, hr, hr2, -, hcrit, -, hstar⟩ := Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hr0 : 0 < paramR q := zero_lt_one.trans hr
  obtain ⟨D, hD0, hD, hemb⟩ := hybrid_compact_embedding (d := d) hα hα1 hr.le hcrit
  let c := 2 * rStarParam (d := d) q t / paramR q
  have hc : 0 < c := div_pos (mul_pos (by norm_num) (hr0.trans hstar)) hr0
  let C3' := C3 + 1
  have hC3' : C3' < ⊤ := ENNReal.add_lt_top.mpr ⟨hC3, by norm_num⟩
  let B := (2 * D * C3') ^ c
  have hpos : 0 < 2 * D * C3' := by
    apply ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) hD0.ne').ne'
    exact (zero_lt_one.trans_le le_add_self).ne'
  refine ⟨B, ENNReal.rpow_pos_of_nonneg hpos hc.le, ENNReal.rpow_lt_top_of_nonneg hc.le
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hD.ne) hC3'.ne), ?_⟩
  intro a ha hrange u G hu huM l₀ l₁ ρ R hl hρ hgap hR
  let wa := fun x => max (u x - l₀) 0
  let Ga := positiveTruncationGradient u G l₀
  have hwa := Selection.source_truncation_pair a ha u G hu l₀
  have hwaM : Measurable wa := (huM.sub measurable_const).max measurable_const
  have hΔ : 0 < l₁ - l₀ := sub_pos.mpr hl
  have hδ : 0 < R - ρ := sub_pos.mpr hgap
  obtain ⟨⟨U, hU, hclU, hae⟩, hfrac, -⟩ := (hloc a ha hrange ρ R hρ hgap hR).2 wa Ga hwa
  have hcov := ((hcover ρ R hρ hgap hR).2)
  let F := fun x => ∑ i ∈ S' ρ R, φ' ρ R i x * wa x
  have hFm : Measurable F := Finset.measurable_sum _ fun i hi =>
    (hcov i hi).2.1.continuous.measurable.mul hwaM
  have hFcs : HasCompactSupport F :=
    hasCompactSupport_finset_sum (S' ρ R) (fun i x => φ' ρ R i x * wa x)
      fun i hi => (hcov i hi).2.2.1.mul_right
  have hAE : wa =ᵐ[volume.restrict (originCube ρ)] F := by
    have := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hclU) hae
    filter_upwards [this] with x hx
    exact hx.symm
  have hcrit_eq : dnpvCriticalExponent d (alphaParam t) (paramR q) = rStarParam (d := d) q t := rfl
  have hlev := hybrid_level_norm_sq (volume.restrict (originCube ρ)) (f := wa) hΔ hr0
    (hcrit_eq ▸ hstar.le : paramR q ≤ dnpvCriticalExponent d (alphaParam t) (paramR q))
    (fun x => le_max_right _ _) hwaM.aestronglyMeasurable
  rw [hcrit_eq] at hlev
  have hYfrac := hybrid_localization_inputs_le_quantity a ha q t ht hq.le u G l₀ R
  have hh : ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
      (weightedEnergy a (originCube R) Ga).rpow (1 / 2) +
      eLpNorm wa (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))) ≤
        2 * twoLevelQuantity a ha q t ht hq.le u G l₀ R := by
    have e : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    simpa only [ENNReal.rpow_eq_pow, e] using hYfrac
  have hnorm : eLpNorm wa (ENNReal.ofReal (rStarParam (d := d) q t))
      (volume.restrict (originCube ρ)) ≤
      (2 * D * C3') * ENNReal.ofReal (R - ρ) ^ (-alphaParam t) *
        twoLevelQuantity a ha q t ht hq.le u G l₀ R := by
    have h1 : eLpNorm wa (ENNReal.ofReal (rStarParam (d := d) q t))
        (volume.restrict (originCube ρ)) ≤
        D * fracNorm Set.univ (alphaParam t) (paramR q) F := by
      calc _ = eLpNorm F (ENNReal.ofReal (rStarParam (d := d) q t))
            (volume.restrict (originCube ρ)) := eLpNorm_congr_ae hAE
        _ ≤ eLpNorm F (ENNReal.ofReal (rStarParam (d := d) q t)) volume :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
        _ ≤ D * fracSeminorm Set.univ (alphaParam t) (paramR q) F := hemb F hFm hFcs
        _ ≤ _ := mul_le_mul_right
            (Foundations.FracGeometry.fracSeminorm_le_fracNorm _ _ hr0 _) D
    refine h1.trans ?_
    refine (mul_le_mul_right hfrac D).trans ?_
    calc D * (C3 * ENNReal.ofReal (R - ρ) ^ (-alphaParam t) *
          ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
            (weightedEnergy a (originCube R) Ga).rpow (1 / 2) +
          eLpNorm wa (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))))
        ≤ D * (C3' * ENNReal.ofReal (R - ρ) ^ (-alphaParam t) *
            (2 * twoLevelQuantity a ha q t ht hq.le u G l₀ R)) := by
          gcongr
          exact le_self_add
      _ = _ := by ring
  have hid : (fun x => max (u x - l₁) 0) = fun x => max (wa x - (l₁ - l₀)) 0 := by
    funext x
    exact (hybrid_positive_level_identity hl.le).symm
  rw [hid]
  refine hlev.trans ?_
  have hpow := ENNReal.rpow_le_rpow hnorm hc.le
  calc ENNReal.ofReal ((l₁ - l₀) ^ (2 - 2 * rStarParam (d := d) q t / paramR q)) *
        eLpNorm wa (ENNReal.ofReal (rStarParam (d := d) q t)) (volume.restrict (originCube ρ)) ^
          (2 * rStarParam (d := d) q t / paramR q)
      ≤ ENNReal.ofReal ((l₁ - l₀) ^ (2 - 2 * rStarParam (d := d) q t / paramR q)) *
        ((2 * D * C3') * ENNReal.ofReal (R - ρ) ^ (-alphaParam t) *
          twoLevelQuantity a ha q t ht hq.le u G l₀ R) ^ c := mul_le_mul_right hpow _
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hc.le, ENNReal.mul_rpow_of_nonneg _ _ hc.le,
        ← ENNReal.rpow_mul, ← ENNReal.ofReal_rpow_of_pos hΔ]
      dsimp only [B, c]
      rw [show -alphaParam t * (2 * rStarParam (d := d) q t / paramR q) =
        -(2 * alphaParam t * rStarParam (d := d) q t / paramR q) by ring]
      ring

end CoarseDeGiorgi.Recurrence
