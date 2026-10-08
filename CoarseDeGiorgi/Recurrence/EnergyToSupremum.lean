import CoarseDeGiorgi.Recurrence.Params
import CoarseDeGiorgi.Assembly.EnergyToSupAdaptive
import CoarseDeGiorgi.Assembly.EnergyToSupReal
import CoarseDeGiorgi.Assembly.EnergyToSupLocal
import CoarseDeGiorgi.Harnack.Moments.MomentComparison
import CoarseDeGiorgi.Statements.LowerFractionalMemLr
import CoarseDeGiorgi.Statements.LocallyBoundedAbove
import CoarseDeGiorgi.Statements.PositivePart
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.TwoLevelQuantity

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Recurrence

open Assembly Aliases

/-- Proposition `p.energy.to.sup` from Proposition `p.two.level.recurrence` (the hypothesis `h82` is
the statement of `CoarseDeGiorgi.two_level_recurrence`, verbatim) and the local `L^r` bound
`lower_fractional_memLr`. -/
theorem energy_to_supremum_of_recurrence (h82 :
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
                        (2 - 2 * rStarParam (d := d) q t / paramR q))) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
          spatialMomentRange a ha p q s t →
          (∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (hu : IsWeightedSubsolution a (originCube 1) u G) →
            ∀ ρ₁ ρ₂ : ℝ, (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              twoLevelQuantity a ha q t ht (le_of_lt hq) u G 0 ρ₂ < ⊤ →
              eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ₁)) ≤
                C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaSup d p q s t) *
                  ENNReal.rpow (contrast a ha s t p q hs ht
                    (le_of_lt hp) (le_of_lt hq))
                    (((d : ℝ) - 3 + 2 * sigmaLower d q t) /
                      (4 * paramTheta d p q s t)) *
                  twoLevelQuantity a ha q t ht (le_of_lt hq) u G 0 ρ₂) ∧
          (∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSubsolution a (originCube 1) u G →
            LocallyBoundedAbove (originCube 1) u) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨hr, hr2, hb, hc, hμ, hcomp⟩ := sup_parameter_facts hd hp hq hs ht hθ
  let μ := ((d : ℝ) - 3 + 2 * sigmaLower d q t) / (4 * paramTheta d p q s t)
  let b := rBoundaryParam (d := d) q t
  let c := 2 * rStarParam (d := d) q t / paramR q
  let g := gammaRec d p q s t
  have hg : 0 < g := gammaRec_pos hd hp hq hs ht hθ
  let γ := gammaSup d p q s t
  have hγdef : γ = 2 * max (g / (b - 2)) (g / (c - 2)) := rfl
  have hMb : 0 < g / (b - 2) := div_pos hg (by linarith)
  have hγ : 0 < γ := by
    rw [hγdef]
    have := (le_max_left (g / (b - 2)) (g / (c - 2)))
    linarith only [this, hMb]
  have heb : 0 ≤ γ * (b - 2) - g := by
    have h1 : g / (b - 2) ≤ γ / 2 := by
      rw [hγdef]; linarith only [le_max_left (g / (b - 2)) (g / (c - 2))]
    have := (div_le_iff₀ (by linarith : 0 < b - 2)).mp h1
    linarith only [this, hg, hb]
  have hec : 0 ≤ γ * (c - 2) - g := by
    have h1 : g / (c - 2) ≤ γ / 2 := by
      rw [hγdef]; linarith only [le_max_right (g / (b - 2)) (g / (c - 2))]
    have := (div_le_iff₀ (by linarith : 0 < c - 2)).mp h1
    linarith only [this, hg, hc]
  let ω := (2 : ℝ) ^ (-γ - 1)
  have hω : 0 < ω := Real.rpow_pos_of_pos (by norm_num) _
  have hω1 : ω < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hratio : (2 : ℝ) ^ γ * ω = 1 / 2 := by
    dsimp only [ω]
    rw [← Real.rpow_add (by norm_num), show γ + (-γ - 1) = -1 by ring]
    norm_num
  have hε : 0 < ω ^ 2 / 4 := by positivity
  have hε1 : ω ^ 2 / 4 < 1 := by nlinarith only [hω, hω1]
  obtain ⟨C, hC, hrecurrence⟩ := h82 (ω ^ 2 / 4) hε hε1 d hd p q s t hp hq hs ht hθ
  obtain ⟨K, hK, hKb, hKc⟩ := energy_to_sup_choose_K (C := C.toReal) hε hb hc
  let Csup := 2 * K * (2 : ℝ) ^ γ
  refine ⟨ENNReal.ofReal Csup, ENNReal.ofReal_lt_top, ?_⟩
  intro a ha hrange
  obtain ⟨hU, hL, hΘ⟩ := caccioppoli_moments_finite hp hq hs ht hrange
  let T := contrast a ha s t p q hs ht hp.le hq.le
  have hTfinite : T ≠ ⊤ := hΘ.ne
  have hT1' : 1 ≤ T := Harnack.Moments.moment_contrast_ge_one (by omega) a ha hs ht hp.le hq.le hU hL
  have hT0 : T ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hT1')
  have hT1 : 1 ≤ T.toReal := by
    have := ENNReal.toReal_mono hTfinite hT1'
    simpa only [ENNReal.toReal_one] using this
  have hlevels : ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
      IsWeightedSubsolution a (originCube 1) u G →
      ∀ ρ R : ℝ, (1 / 2 : ℝ) ≤ ρ → ρ < R → R ≤ 1 →
      twoLevelQuantity a ha q t ht hq.le u G 0 R < ⊤ →
      ∃ L : ℝ, 0 ≤ L ∧
        L ≤ 2 * K * T.toReal ^ μ * ((R - ρ) / 2) ^ (-γ) *
          (twoLevelQuantity a ha q t ht hq.le u G 0 R).toReal ∧
        twoLevelQuantity a ha q t ht hq.le u G L ρ = 0 := by
    intro u G hu ρ R hρ hρR hR hfinite
    apply energy_to_sup_adaptive (Q := fun l r => twoLevelQuantity a ha q t ht hq.le u G l r)
      hρR (by linarith only [hρ, hR]) C.toReal_nonneg hK hT1 hμ.le hγ hω hω1
      hratio heb hec hcomp hc hKb hKc hfinite
    · intro l k r z hl hlk hρr hrz hzR
      exact energy_to_sup_quantity_mono ha q t ht hq.le u G hu.1.1 hlk hrz (hzR.trans hR)
    · intro l k r z hl hlk hρr hrz hzR hX0
      have hXfinite : twoLevelQuantity a ha q t ht hq.le u G l z < ⊤ :=
        (energy_to_sup_quantity_mono ha q t ht hq.le u G hu.1.1 hl hzR hR).trans_lt hfinite
      have hh := hrecurrence a ha hrange u G hu l k r z hl hlk (hρ.trans hρr) hrz
        (hzR.trans hR) hXfinite
      exact energy_to_sup_recurrence_toReal hC.ne hTfinite hT0 hXfinite.ne hX0
        (sub_pos.mpr hrz) (sub_pos.mpr hlk) hε.le hh
  constructor
  · intro u G hu ρ R hρ hρR hR hfinite
    obtain ⟨L, hL0, hLbound, hzero⟩ := hlevels u G hu ρ R hρ hρR hR hfinite
    have hs := (energy_to_sup_zero_bound a ha q t ht hq.le hr u G hu.1.1
      (hρR.le.trans hR) hL0 hzero).1
    apply hs.trans
    apply (ENNReal.ofReal_le_ofReal hLbound).trans_eq
    have hδ := sub_pos.mpr hρR
    have hid : ((R - ρ) / 2) ^ (-γ) = (2 : ℝ) ^ γ * (R - ρ) ^ (-γ) := by
      rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (x := (2 : ℝ)) (by norm_num), div_inv_eq_mul]
      ring
    rw [hid]
    have ht0 : 0 < T.toReal := by linarith only [hT1]
    calc
      _ = ENNReal.ofReal (Csup * (R - ρ) ^ (-γ) * T.toReal ^ μ *
          (twoLevelQuantity a ha q t ht hq.le u G 0 R).toReal) := by congr 1; dsimp [Csup]; ring
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfinite.ne,
          ← ENNReal.ofReal_rpow_of_pos hδ, ← ENNReal.ofReal_rpow_of_pos ht0,
          ENNReal.ofReal_toReal hTfinite]
        rfl
  · intro u G hu Kcompact hK hKV
    obtain ⟨ρ, hρ, hρ1, hKρ⟩ := energy_to_sup_compact_cube hK hKV
    let R := (ρ + 1) / 2
    have hρR : ρ < R := by dsimp [R]; linarith only [hρ1]
    have hR1 : R < 1 := by dsimp [R]; linarith only [hρ1]
    let J : Set (Vec d) := Set.pi Set.univ (fun _ => Set.Icc (-(R / 2)) (R / 2))
    have hJV : J ⊆ originCube 1 := by
      intro x hx i
      have hi := hx i (Set.mem_univ i)
      constructor <;> linarith only [hi.1, hi.2, hR1]
    have hRJ : originCube R ⊆ J := by
      intro x hx i _
      exact ⟨(hx i).1.le, (hx i).2.le⟩
    have hLr := lower_fractional_memLr hd p q s t a ha hrange u G hu.1
    have hLrR : MemLp u (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) :=
      lt_of_le_of_lt (eLpNorm_mono_measure u (Measure.restrict_mono (hRJ.trans hJV) le_rfl)) hLr
    have hfinite := energy_to_sup_initial_finite ht hq.le hu hL hR1.le hLrR
    obtain ⟨L, hL0, _, hzero⟩ := hlevels u G hu ρ R hρ hρR hR1.le hfinite
    refine ⟨L, ae_restrict_of_ae_restrict_of_subset hKρ ?_⟩
    exact (energy_to_sup_zero_bound a ha q t ht hq.le hr u G hu.1.1
      (hρR.le.trans hR1.le) hL0 hzero).2

end CoarseDeGiorgi.Recurrence
