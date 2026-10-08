module

public import CoarseDeGiorgi.Recurrence.Approx
public import CoarseDeGiorgi.Recurrence.Params
public import CoarseDeGiorgi.Assembly.HybridSurfaceBounds
public import CoarseDeGiorgi.Assembly.HybridSurfaceArithmetic
public import CoarseDeGiorgi.Assembly.HybridBulkQuantity
public import CoarseDeGiorgi.Assembly.HybridQuantity
public import CoarseDeGiorgi.Assembly.EnergyToSupQuantity
public import CoarseDeGiorgi.Selection.SourceTraces
public import CoarseDeGiorgi.Weighted.TestingTruncation
public import CoarseDeGiorgi.Statements.GoodRadiusExists
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.TwoLevelQuantity
public import CoarseDeGiorgi.Statements.PositiveCap
public import CoarseDeGiorgi.Statements.PositiveCapGradient
public import CoarseDeGiorgi.Statements.SampledResponseSeries
public import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import CoarseDeGiorgi.Statements.SurfaceFracNorm
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.SurfaceMeasure
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.GammaLoc

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Recurrence

open Assembly

/-- Steps 1 and 2 of Proposition `p.two.level.recurrence` before the choice of `h`: the energy of
the truncation at the level `l₁` on a good cube, from Proposition `p.good.radius`
and Proposition `p.good.radius.energy` (the hypothesis `h72`, restricted to narrower widths). -/
theorem energy_step_of_energy (h72 :

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
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSubsolution a (originCube 1) u G → Measurable u →
            ∀ l₀ l₁ ρ R : ℝ, l₀ < l₁ → 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
              twoLevelQuantity a ha q t ht hq.le u G l₀ R ≠ ⊤ →
              ∀ k : ℤ, (3 : ℝ) ^ k ≤ (R - ρ) / (20000 * (d : ℝ)) →
                (lowerMoment a ha t q ht hq.le) ^ (-1 : ℝ) *
                    weightedEnergy a (originCube ρ) (positiveTruncationGradient u G l₁) ≤
                  C * ENNReal.ofReal (R - ρ) ^ (-gammaLoc p q t) *
                      contrast a ha s t p q hs ht hp.le hq.le ^ (1 / 2 : ℝ) *
                      ENNReal.ofReal ((3 : ℝ) ^ k) ^ (paramTheta d p q s t) *
                      twoLevelQuantity a ha q t ht hq.le u G l₀ R ^ (2 : ℝ) +
                    C * ENNReal.ofReal (R - ρ) ^
                        (-(1 / (2 * p) + 1 / 2 +
                          (alphaParam t + 1 / paramR q) *
                            rBoundaryParam (d := d) q t / 2)) *
                      contrast a ha s t p q hs ht hp.le hq.le ^ (1 / 2 : ℝ) *
                      ENNReal.ofReal ((3 : ℝ) ^ k) ^ (-(sigmaUpper d p s)) *
                      twoLevelQuantity a ha q t ht hq.le u G l₀ R ^
                        (1 + rBoundaryParam (d := d) q t / 2) *
                      ENNReal.ofReal (l₁ - l₀) ^
                        (1 - rBoundaryParam (d := d) q t / 2) := by
  intro d hd p q s t hp hq hs ht hθ
  have : NeZero d := ⟨by omega⟩
  obtain ⟨K, hK, hK72⟩ := h72 d hd p q s t hp hq hs ht hθ
  obtain ⟨C₅, hC₅, hGR⟩ := CoarseDeGiorgi.good_radius_exists d hd p q s t hp hq hs ht hθ
  obtain ⟨hα, hα1, hr, _, hcrit, _, hz, _⟩ := Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  obtain ⟨A, hA, hlevel⟩ := hybrid_selected_level_bounds hα hα1 hr hcrit hz.le
  let Kf := C₅ * 2
  let Kl := A * Kf ^ (rBoundaryParam (d := d) q t / 2)
  let Kd := C₅ ^ (1 / 2 : ℝ)
  let C := K * C₅ * Kd * (Kf + Kl)
  have hz0 : 0 ≤ rBoundaryParam (d := d) q t := (by norm_num : (0 : ℝ) ≤ 2).trans hz.le
  have hKd : Kd < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC₅.ne
  have hKf : Kf < ⊤ := ENNReal.mul_lt_top hC₅ (by norm_num)
  have hKl : Kl < ⊤ := ENNReal.mul_lt_top hA (ENNReal.rpow_lt_top_of_nonneg (by positivity) hKf.ne)
  have hC : C < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK hC₅) hKd)
    (ENNReal.add_lt_top.mpr ⟨hKf, hKl⟩)
  refine ⟨C, hC, ?_⟩
  intro a ha hrange u G hu huM l₀ l₁ ρ R hl hρ hgap hR hY k hk
  let wa := fun x => max (u x - l₀) 0
  let wb := fun x => max (u x - l₁) 0
  let Ga := positiveTruncationGradient u G l₀
  let Gb := positiveTruncationGradient u G l₁
  have hunit := hybrid_unitCube_domain (d := d)
  have hwa := Selection.source_truncation_pair a ha u G hu.1 l₀
  have hwb : IsWeightedSubsolution a (originCube 1) wb Gb :=
    Weighted.IsWeightedSubsolution.max_sub_const hunit.1 hunit.2 ha hu l₁
  have hwaM : Measurable wa := (huM.sub measurable_const).max measurable_const
  have hδ : 0 < R - ρ := sub_pos.mpr hgap
  have hδ1 : R - ρ ≤ 1 := by linarith only [hρ, hR]
  have hΔ : 0 < l₁ - l₀ := sub_pos.mpr hl
  have hwa0 : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), 0 ≤ wa x :=
    Eventually.of_forall fun _ => le_max_right _ _
  have hYnorm : eLpNorm wa (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) ≤
      twoLevelQuantity a ha q t ht hq.le u G l₀ R :=
    energy_to_sup_norm_le_quantity a ha q t ht hq.le u G l₀ R
  have hLrFin : eLpNorm wa (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) < ⊤ :=
    lt_of_le_of_lt hYnorm (lt_top_iff_ne_top.mpr hY)
  obtain ⟨vi, hvi, hvi0, hvilim⟩ := smooth_approx a ha hwa hwa0
  obtain ⟨τ, hτ, ns, hns, hconv, hS, hD, hFrac, -, hmax, -⟩ :=
    hGR a ha hrange wa Ga hwa hwa0 ρ R hρ hgap hR hLrFin vi hvi hvi0 hvilim
  have hτouter := Selection.selectionInterval_subset hgap hτ
  have hτhalf : 1 / 2 ≤ τ := hρ.trans hτouter.1.le
  have hτ1 : τ ≤ 1 := hτouter.2.le.trans hR
  -- the truncation at the level `Δ` of `wa` is `wb`
  have hcap : positiveCap wa (l₁ - l₀) ⊤ = wb := by
    funext x
    simp only [positiveCap, ↓reduceIte, positivePart, wa, wb]
    exact hybrid_positive_level_identity hl.le
  have hcapG : positiveCapGradient wa Ga (l₁ - l₀) ⊤ = Gb := by
    funext x
    simp only [positiveCapGradient, ↓reduceIte, positiveTruncationGradient, Ga, Gb, wa]
    by_cases hx : l₁ < u x
    · have h1 : l₀ < u x := hl.trans hx
      have h2 : l₁ - l₀ < max (u x - l₀) 0 := lt_max_of_lt_left (by linarith only [hx])
      simp only [hx, h1, h2, ↓reduceIte]
    · have h2 : ¬ (l₁ - l₀ < max (u x - l₀) 0) := by
        rw [not_lt]
        exact max_le (by linarith only [not_lt.mp hx]) hΔ.le
      simp only [hx, h2, ↓reduceIte]
  have hsub : IsWeightedSubsolution a (originCube 1) (positiveCap wa (l₁ - l₀) ⊤)
      (positiveCapGradient wa Ga (l₁ - l₀) ⊤) := by
    rw [hcap, hcapG]; exact hwb
  -- the triadic width
  have hkneg : k ≤ 0 := by
    by_contra hk0
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_zpow₀ (by norm_num) (le_of_lt (not_le.mp hk0))
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have h2 : (R - ρ) / (20000 * (d : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith only [hδ1, hd3]
    linarith only [hk, h1, h2]
  have htri : IsTriadicWidth ((3 : ℝ) ^ k) := ⟨(-k).toNat, by
    congr 1; omega⟩
  have henergy := hK72 a ha hrange wa Ga hwa hwa0 ρ R hρ hgap hR hLrFin vi hvi hvi0 hvilim τ hτ
    ns hns C₅ hC₅ hconv hS hD hmax (l₁ - l₀) hsub ((3 : ℝ) ^ k) htri hk
  rw [hcap, hcapG] at henergy
  have hinner := (lintegral_mono_set (caccioppoli_cube_mono hτouter.1.le)).trans henergy
  -- the ingredients of the normalized surface bound
  have hMom := caccioppoli_moments_finite (a := a) (ha := ha) hp hq hs ht hrange
  have hGaFin : weightedEnergy a (originCube R) Ga < ⊤ := by
    exact (lintegral_mono_set (caccioppoli_cube_mono hR)).trans_lt
      (Weighted.MemH1a.energy_lt_top hunit.1.isOpen ha hwa)
  let Y := twoLevelQuantity a ha q t ht hq.le u G l₀ R
  let b := alphaParam t + 1 / paramR q
  have hYfrac := hybrid_localization_inputs_le_quantity a ha q t ht hq.le u G l₀ R
  have hFracBound : surfaceFracNorm τ (alphaParam t) (paramR q) wa ≤
      Kf * ENNReal.ofReal (R - ρ) ^ (-b) * Y := by
    refine hFrac.trans ?_
    have h2 := hYfrac
    have hh : ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
        (weightedEnergy a (originCube R) Ga).rpow (1 / 2) +
        eLpNorm wa (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))) ≤ 2 * Y := by
      have e : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
      simpa only [ENNReal.rpow_eq_pow, e] using h2
    have hexp : -alphaParam t - 1 / paramR q = -b := by dsimp only [b]; ring
    simp only [hexp]
    calc C₅ * ENNReal.ofReal (R - ρ) ^ (-b) * (_ + _) ≤ C₅ * ENNReal.ofReal (R - ρ) ^ (-b) * (2 * Y) := by
          gcongr
      _ = Kf * ENNReal.ofReal (R - ρ) ^ (-b) * Y := by
          dsimp only [Kf]; ring
  have hlevelBound := hlevel τ (R - ρ) (l₁ - l₀) b Kf Y wa hτhalf hτ1 hΔ hwaM
    (fun x => le_max_right _ _) hFracBound
  have hid : (fun x => max (wa x - (l₁ - l₀)) 0) = wb := by
    funext x
    exact hybrid_positive_level_identity hl.le
  rw [hid] at hlevelBound
  have hFb : surfaceFracSeminorm τ (alphaParam t) (paramR q) wb ≤
      Kf * ENNReal.ofReal (R - ρ) ^ (-b) * Y := hlevelBound.1
  have hZb : eLpNorm wb 2 (surfaceMeasure τ) ≤
      Kl * ENNReal.ofReal (R - ρ) ^ (-b * rBoundaryParam (d := d) q t / 2) *
        Y ^ (rBoundaryParam (d := d) q t / 2) *
          ENNReal.ofReal (l₁ - l₀) ^ (1 - rBoundaryParam (d := d) q t / 2) := by
    have hZbase := hlevelBound.2
    change eLpNorm wb 2 (surfaceMeasure τ) ≤
      A * (Kf * ENNReal.ofReal (R - ρ) ^ (-b) * Y) ^ (rBoundaryParam (d := d) q t / 2) *
        ENNReal.ofReal (l₁ - l₀) ^ (1 - rBoundaryParam (d := d) q t / 2) at hZbase
    refine hZbase.trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    dsimp only [Kl]
    ring_nf
  have hDb : (surfaceEnergyMaximal ρ R a ha Ga τ) ^ (1 / 2 : ℝ) ≤
      Kd * ENNReal.ofReal (R - ρ) ^ (-1 / 2 : ℝ) *
        weightedEnergy a (originCube R) Ga ^ (1 / 2 : ℝ) := by
    refine (ENNReal.rpow_le_rpow hD (by norm_num)).trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.inv_rpow,
      show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, ENNReal.rpow_neg]
  have hS' : sampledResponseSeries a ha s p τ ≤
      C₅ * ENNReal.ofReal (R - ρ) ^ (-(1 / (2 * p))) *
        (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) := hS
  have hnorm := hybrid_normalized_surface_bound (θ := paramTheta d p q s t)
    (m := sigmaUpper d p s) (Δ := l₁ - l₀) (h := (3 : ℝ) ^ k) (L := lowerMoment a ha t q ht hq.le)
    hδ hz0 hS' hDb hFb hZb
    (hybrid_weighted_part_le_quantity a ha q t ht hq.le u G l₀ R) hinner
  have hexp1 : 1 / (2 * p) + 1 / 2 + b = gammaLoc p q t := by
    have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
    have hq1 : q + 1 ≠ 0 := by linarith only [hq]
    dsimp only [b]
    unfold gammaLoc alphaParam paramR
    field_simp
    ring
  have hexp2 : 1 / (2 * p) + 1 / 2 + b * rBoundaryParam (d := d) q t / 2 =
      1 / (2 * p) + 1 / 2 + (alphaParam t + 1 / paramR q) * rBoundaryParam (d := d) q t / 2 := by
    rfl
  rw [hexp1, hexp2] at hnorm
  have hKc₁ : K * C₅ * Kd * Kf ≤ C := by
    dsimp only [C]; gcongr; exact le_add_right le_rfl
  have hKc₂ : K * C₅ * Kd * Kl ≤ C := by
    dsimp only [C]; gcongr; exact le_add_left le_rfl
  refine hnorm.trans ?_
  dsimp only [contrast, Y]
  gcongr

end CoarseDeGiorgi.Recurrence
