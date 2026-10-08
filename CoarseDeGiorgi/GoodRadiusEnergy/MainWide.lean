module

public import CoarseDeGiorgi.ExteriorIntegral.MainWide
public import CoarseDeGiorgi.GoodRadiusEnergy.TraceL2
public import CoarseDeGiorgi.GoodRadiusEnergy.Approx
public import CoarseDeGiorgi.GoodRadiusEnergy.Glue
public import CoarseDeGiorgi.GoodRadiusEnergy.Limit
public import CoarseDeGiorgi.Whitney.LiftTestingLimit
public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import CoarseDeGiorgi.Whitney.SourceWitnessCore
public import CoarseDeGiorgi.Whitney.ExteriorCells
public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.TraceControl
public import CoarseDeGiorgi.PowerCacc.OneSurface
public import CoarseDeGiorgi.Selection.SourceRadius

/-! # Proposition `p.good.radius.energy` (`good_radius_energy_bound`) from the three extension statements

The testing argument with the glued extension of Proposition `p.whitney.extension`: for each smooth
approximant `vᵢ`, the function equal to `(vᵢ - k)₊` on `τ□̄₀` and to the piecewise harmonic
extension of its trace outside is a nonnegative test function; Lemma `l.exterior.integral` bounds
the exterior pairing; only the numbers (pairings and surface norms) pass to the limit along the
subsequence. -/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.GoodRadiusEnergy.WideWidth

open GoodRadiusEnergy

open scoped Classical in
theorem good_radius_energy_bound_of_extension
    (h71 : ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
            ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
              let hτ0 : (1 / 2 : ℝ) ≤ τ := by
                have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
                linarith
              let hτ1 : τ < 1 := by
                have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
                linarith
              ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (200 * (d : ℝ)) →
                ∀ (g : Vec d → ℝ),
                  (∃ K : ℝ≥0, LipschitzOnWith K g (cubeSurface τ)) →
                    ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
                      MemH1a a (originCube 1) v G →
                      ∀ (H : Vec d → ℝ) (GH : Vec d → Vec d),
                        IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 g H GH →
                        Integrable (fun x => vecDot (GH x) (matVecMul (a x) (G x)))
                          (volume.restrict (originCube 1 \ closedReferenceCube (d := d) τ)) ∧
                        ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube (d := d) τ,
                          vecDot (GH x) (matVecMul (a x) (G x))| ≤
                          C * sampledResponseSeries a ha s p τ *
                            (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                            ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                              surfaceFracSeminorm τ (alphaParam t) (paramR q) g +
                              (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                                eLpNorm g 2 (surfaceMeasure τ)) ∧
                        ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube (d := d) τ,
                          vecDot (GH x) (matVecMul (a x) (G x))| ≤
                          C * sampledResponseSeries a ha s p τ *
                            (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                            ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                              surfaceFracSeminorm τ (alphaParam t) (paramR q) g +
                              (ENNReal.ofReal h).rpow
                                (-(sigmaUpper d p s + sigmaLower d q t - t)) *
                                eLpNorm g (ENNReal.ofReal (paramR q)) (surfaceMeasure τ)))
    (h62 : ∀ (d : ℕ) (_hd : 3 ≤ d) (α ξ : ℝ)
    (_hα0 : 0 < α) (_hα1 : α < 1) (_hξ1 : 1 ≤ ξ) (_hξ2 : ξ ≤ 2),
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
      ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
          let hτ0 : (1 / 2 : ℝ) ≤ τ := by
            have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
            linarith
          let hτ1 : τ < 1 := by
            have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
            linarith
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (100 * (d : ℝ)) →
            -- linearity in `f`
            (∀ f₁ f₂ : Vec d → ℝ,
              (∃ K : ℝ≥0, LipschitzOnWith K f₁ (cubeSurface τ)) →
              (∃ K : ℝ≥0, LipschitzOnWith K f₂ (cubeSurface τ)) →
              ∀ c₁ c₂ : ℝ,
              ∀ (H₁ H₂ H : Vec d → ℝ) (GH₁ GH₂ GH : Vec d → Vec d),
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f₁ H₁ GH₁ →
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f₂ H₂ GH₂ →
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1
                  (fun y => c₁ * f₁ y + c₂ * f₂ y) H GH →
                ∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) τ)ᶜ),
                  H x = c₁ * H₁ x + c₂ * H₂ x ∧ GH x = c₁ • GH₁ x + c₂ • GH₂ x) ∧
            ∀ f : Vec d → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K f (cubeSurface τ)) →
            ∀ (H : Vec d → ℝ) (GH : Vec d → Vec d),
              IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH →
              -- nonnegativity
              ((∀ y ∈ cubeSurface (d := d) τ, 0 ≤ f y) →
                ∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) τ)ᶜ), 0 ≤ H x) ∧
              -- the range bound of `L_h f`
              (∀ m M : ℝ, m ≤ 0 → 0 ≤ M →
                (∀ y ∈ cubeSurface (d := d) τ, m ≤ f y ∧ f y ≤ M) →
                ∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) τ)ᶜ),
                  m ≤ H x ∧ H x ≤ M) ∧
              -- ordinary trace `f` on `∂(τ□₀)`
              (∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube (d := d) 1 →
                ∫ x in originCube (d := d) 1 \ closedReferenceCube (d := d) τ,
                    (H x * fderiv ℝ φ x (basisVec i) + GH x i * φ x) =
                  (∫ x, f x * φ x ∂(cubeFaceMeasure τ i false)) -
                    ∫ x, f x * φ x ∂(cubeFaceMeasure τ i true)) ∧
              -- `H_h f ∈ W^{1,1}(□₀ ∖ τ□̄₀)` with finite energy
              (Integrable H (volume.restrict
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ)) ∧
                Integrable GH (volume.restrict
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ)) ∧
                HasWeakGradientOn
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ) H GH ∧
                weightedEnergy a
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ) GH < ⊤) ∧
              -- vanishes outside `(τ + 3h)□̄₀`
              (∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) (τ + 3 * h))ᶜ),
                H x = 0) ∧
              -- `e.harmonic.energy`
              (∀ (j : ℕ) (cell : ExteriorCell d τ),
                cell ∈ whitneySimplicesNearSize (d := d) τ h j →
                ∃ η : SimplexIndex d j, exteriorCellSet cell = simplexCell j η ∧
                  ∀ x ∈ exteriorCellSet cell,
                    weightedEnergy a (exteriorCellSet cell) GH =
                      volume (exteriorCellSet cell) *
                        ENNReal.ofReal
                          (vecDot (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)
                            (matVecMul (upperResponseOnCell j a ha η)
                              (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x))) ∧
                    volume (exteriorCellSet cell) *
                        ENNReal.ofReal
                          (vecDot (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)
                            (matVecMul (upperResponseOnCell j a ha η)
                              (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x))) ≤
                      sampledUpperResponse a ha j τ *
                        (volume (exteriorCellSet cell) *
                          ENNReal.ofReal (vecNormSq
                            (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)))) ∧
              -- the estimate `e.extension.scale` with the extra factor `A_j(τ)`
              (∀ (j : ℕ) (b : ℝ), (b = 2 ∨ b = ξ) →
                ∑' cell : whitneySimplicesNearSize (d := d) τ h j,
                  weightedEnergy a (exteriorCellSet cell.1) GH ≤
                  sampledUpperResponse a ha j τ *
                    (C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
                      (ENNReal.ofReal ((3 : ℝ) ^ (j : ℤ) *
                          (3 : ℝ) ^ (-((j : ℝ) *
                            (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2))))) *
                        surfaceFracSeminorm τ α ξ f) ^ 2 +
                    C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
                      (ENNReal.ofReal (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) *
                          (((d : ℝ) - 1) * (1 / b - 1 / 2)))) *
                        eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ)) ^ 2)) ∧
              -- gluing with a Lipschitz `w` on `τ□̄₀`
              (∀ w : Vec d → ℝ,
                (∃ K : ℝ≥0, LipschitzOnWith K w (closedReferenceCube (d := d) τ)) →
                (∀ y ∈ cubeSurface (d := d) τ, w y = f y) →
                ∃ G : Vec d → Vec d,
                  MemH1a0 a (originCube (d := d) 1)
                    (fun x => if x ∈ closedReferenceCube (d := d) τ then w x else H x) G ∧
                  (∃ K : Set (Vec d), IsCompact K ∧ K ⊆ originCube (d := d) ρ₂ ∧
                    ∀ᵐ x ∂volume, x ∉ K →
                      (if x ∈ closedReferenceCube (d := d) τ then w x else H x) = 0) ∧
                  ((∀ x ∈ closedReferenceCube (d := d) τ, 0 ≤ w x) →
                    ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)),
                      0 ≤ (if x ∈ closedReferenceCube (d := d) τ then w x else H x))))
    (hex : ∀ d : ℕ, 3 ≤ d → ∀ a : CoeffField d,
      IsWeightedCoeffOn (originCube 1) a →
      ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
          let hτ0 : (1 / 2 : ℝ) ≤ τ := by
            have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
            linarith
          let hτ1 : τ < 1 := by
            have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
            linarith
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (100 * (d : ℝ)) →
            ∀ f : Vec d → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K f (cubeSurface τ)) →
              ∃ (H : Vec d → ℝ) (GH : Vec d → Vec d),
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH) :
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
                    ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (200 * (d : ℝ)) →
                      weightedEnergy a (originCube τ) (positiveCapGradient v G k ⊤) ≤
                        C * sampledResponseSeries a ha s p τ *
                          (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                          ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                            surfaceFracSeminorm τ (alphaParam t) (paramR q)
                              (positiveCap v k ⊤) +
                            (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                              eLpNorm (positiveCap v k ⊤) 2 (surfaceMeasure τ)) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have : NeZero (n + 1) := ⟨by omega⟩
  obtain ⟨hα0, hα1, -, -⟩ := PowerCacc.power_surface_parameters hd hp hq hs ht hθ
  have hr := Assembly.theoremA_paramR_range hq
  obtain ⟨Cext, hCext, hext⟩ := h71 (n + 1) hd p q s t hp hq hs ht hθ
  obtain ⟨_, _, h62a⟩ := h62 (n + 1) hd (alphaParam t) (paramR q) hα0 hα1 hr.1.le hr.2.le
  refine ⟨Cext, hCext, ?_⟩
  intro a ha hrange v G hv hvnonneg ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ hY vi hvi hvinn hnorm τ hτ ns hns C₅ hC₅
    hconv hS hD hDmono k hsub h htri hwidth
  obtain ⟨hV, hne⟩ := Assembly.theoremA_unitCube_domain (n + 1)
  have hh : 0 < h := by
    obtain ⟨m, hm⟩ := htri
    rw [hm]
    positivity
  have hδ : 0 < ρ₂ - ρ₁ := sub_pos.mpr hρ₁₂
  have hτ0 : (1 / 2 : ℝ) ≤ τ := by
    have h1 := hτ.1
    linarith
  have hwidthExt : h ≤ (ρ₂ - τ) / (100 * (((n + 1 : ℕ) : ℝ))) := by
    have hdreal : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hb := (le_div_iff₀ (by positivity : (0 : ℝ) < 200 * (((n + 1 : ℕ) : ℝ)))).mp hwidth
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 100 * (((n + 1 : ℕ) : ℝ)))).mpr
    linarith only [hb, hτ.2]
  have hτI := CoarseDeGiorgi.Selection.selectionInterval_subset hρ₁₂ hτ
  have hτpos : 0 < τ := by linarith only [hτ0]
  have hτone : τ < 1 := hτI.2.trans_le hρ₂
  have hwsub : originCube (d := n + 1) τ ⊆ originCube 1 :=
    Assembly.caccioppoli_cube_mono hτone.le
  -- finiteness of the selected-radius quantities
  have hmom := Assembly.caccioppoli_moments_finite (a := a) (ha := ha) hp hq hs ht hrange
  have hER : weightedEnergy a (originCube ρ₂) G < ⊤ :=
    (Assembly.caccioppoli_energy_mono a G hρ₂).trans_lt
      (Weighted.MemH1a.energy_lt_top hV.isOpen ha hv)
  have hrp (y : ℝ) : (ENNReal.ofReal (ρ₂ - ρ₁)).rpow y < ⊤ := by
    simp only [ENNReal.rpow_eq_pow]
    rw [ENNReal.ofReal_rpow_of_pos hδ]
    exact ENNReal.ofReal_lt_top
  have hSfin : sampledResponseSeries a ha s p τ < ⊤ := hS.trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC₅ (hrp _))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmom.1.ne))
  have hDfin : surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ < ⊤ := hD.trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC₅
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hδ))) hER)
  have hK₀ : Cext * sampledResponseSeries a ha s p τ *
      (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hCext hSfin)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hDfin.ne)
  have hDw : surfaceEnergyMaximal ρ₁ ρ₂ a ha (positiveCapGradient v G k ⊤) τ ≤
      surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ := hDmono k ⊤ ENNReal.zero_lt_top τ
  -- the approximants
  obtain ⟨hmemi, hL1, hEn⟩ := trunc_approx_tendsto ha hv vi hvi hnorm k
  have hLip (i : ℕ) : ∃ K' : ℝ≥0, LipschitzOnWith K'
      (positiveCap (vi (ns i)) k ⊤) (closedReferenceCube τ) := by
    obtain ⟨K1, hK1⟩ := PowerCacc.lipschitzOn_closedReferenceCube_of_isSmoothCore hτone
      (hvi (ns i))
    refine ⟨1 * K1, ?_⟩
    rw [positiveCap_top_eq]
    exact (lipschitzWith_posPart k).comp_lipschitzOnWith hK1
  have hLipSurf (i : ℕ) : ∃ K' : ℝ≥0, LipschitzOnWith K'
      (positiveCap (vi (ns i)) k ⊤) (cubeSurface τ) := by
    obtain ⟨K', hK'⟩ := hLip i
    exact ⟨K', hK'.mono (PowerCacc.cubeSurface_subset_closedReferenceCube τ)⟩
  have hwSurf (i : ℕ) : AEStronglyMeasurable (positiveCap (vi (ns i)) k ⊤)
      (surfaceMeasure τ) := by
    obtain ⟨K', hK'⟩ := hLipSurf i
    exact (Whitney.seedSurface_integrable_of_continuousOn hτpos.le
      hK'.continuousOn).aestronglyMeasurable
  -- one test per approximant
  have htests : ∀ i, ∃ GHx : Vec (n + 1) → Vec (n + 1),
      (∫ x in originCube τ, vecDot (positiveCapGradient (vi (ns i)) (smoothGrad (vi (ns i))) k ⊤ x)
          (matVecMul (a x) (positiveCapGradient v G k ⊤ x))) ≤
        |∫ x in originCube 1 \ closedReferenceCube τ,
          vecDot (GHx x) (matVecMul (a x) (positiveCapGradient v G k ⊤ x))| ∧
      ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube τ,
          vecDot (GHx x) (matVecMul (a x) (positiveCapGradient v G k ⊤ x))| ≤
        (Cext * sampledResponseSeries a ha s p τ *
          (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2)) *
        ((ENNReal.ofReal h).rpow (paramTheta (n + 1) p q s t) *
            surfaceFracSeminorm τ (alphaParam t) (paramR q) (positiveCap (vi (ns i)) k ⊤) +
          (ENNReal.ofReal h).rpow (-(sigmaUpper (n + 1) p s)) *
            eLpNorm (positiveCap (vi (ns i)) k ⊤) 2 (surfaceMeasure τ)) := by
    intro i
    obtain ⟨Hx, GHx, hrep⟩ := hex (n + 1) hd a ha ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ τ hτ h htri hwidthExt
      _ (hLipSurf i)
    have h71i := hext a ha hrange ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ τ hτ h htri hwidth _ (hLipSurf i)
      _ _ hsub.1 Hx GHx hrep
    have h62i := (h62a a ha ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ τ hτ h htri hwidthExt).2 _ (hLipSurf i)
      Hx GHx hrep
    obtain ⟨-, -, -, hW11, -, -, -, hglue⟩ := h62i
    refine ⟨GHx, ?_, ?_⟩
    · exact glued_test_inner_le ha hsub hτpos hτone (hmemi (ns i))
        (fun x => by rw [positiveCap_top_eq]; exact le_max_right _ _) (hLip i)
        hW11.2.1 hW11.2.2.1 hglue
    · refine h71i.2.1.trans ?_
      gcongr
      exact ENNReal.rpow_le_rpow hDw (by norm_num)
  choose GHx hP hB using htests
  -- the limit
  have hGE : weightedEnergy a (originCube 1) (positiveCapGradient v G k ⊤) < ⊤ :=
    Weighted.MemH1a.energy_lt_top hV.isOpen ha hsub.1
  have hEτ : weightedEnergy a (originCube τ) (positiveCapGradient v G k ⊤) < ⊤ :=
    (lintegral_mono_set hwsub).trans_lt hGE
  have hPlim := Whitney.lift_interior_pairing_tendsto (W := originCube τ) ha hwsub
    (fun i => positiveCapGradient (vi (ns i)) (smoothGrad (vi (ns i))) k ⊤)
    (positiveCapGradient v G k ⊤) (fun i => (hmemi (ns i)).2.1) hsub.1.2.1
    (fun i => Weighted.MemH1a.energy_lt_top hV.isOpen ha (hmemi (ns i))) hGE
    (hEn.comp hns.tendsto_atTop)
  have hc₁0 : (ENNReal.ofReal h).rpow (paramTheta (n + 1) p q s t) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hh) ENNReal.ofReal_ne_top).ne'
  have hc₂0 : (ENNReal.ofReal h).rpow (-(sigmaUpper (n + 1) p s)) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hh) ENNReal.ofReal_ne_top).ne'
  have hc₁ : (ENNReal.ofReal h).rpow (paramTheta (n + 1) p q s t) < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hθ.le ENNReal.ofReal_ne_top)
  have hc₂ : (ENNReal.ofReal h).rpow (-(sigmaUpper (n + 1) p s)) < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top)
  refine energy_le_of_pairings hEτ hK₀ hc₁ hc₂ hc₁0 hc₂0
    (fun i => surfaceFracSeminorm τ (alphaParam t) (paramR q) (positiveCap (vi (ns i)) k ⊤))
    (fun i => eLpNorm (positiveCap (vi (ns i)) k ⊤) 2 (surfaceMeasure τ))
    _ _ hPlim hP hB ?_
  intro hF hL ε hε
  have hTraceFrac := hconv k ⊤ ENNReal.zero_lt_top
  have hwS : AEStronglyMeasurable (positiveCap v k ⊤) (surfaceMeasure τ) :=
    aestronglyMeasurable_of_eLpNorm_ne_top hL.ne
  have hTraceL2 := trace_l2_tendsto hd hp hq hs ht hθ hτ0 hτone.le
    (fun i => (hwSurf i).sub hwS) hTraceFrac
  have hsemi := Harnack.PowerCaccioppoli.surfaceFracSeminorm_eventually_close_of_tendsto
    (τ := τ) (α := alphaParam t) hr.1 (positiveCap v k ⊤)
    (fun i => positiveCap (vi (ns i)) k ⊤) hwS hwSurf hF hTraceFrac ε hε
  have hL2ev := (tendsto_order.1 hTraceL2).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  filter_upwards [hsemi, hL2ev] with i h1 h2
  refine ⟨h1, ?_⟩
  have hsum : positiveCap (vi (ns i)) k ⊤ = positiveCap v k ⊤ +
      (fun x => positiveCap (vi (ns i)) k ⊤ x - positiveCap v k ⊤ x) := by
    ext x
    simp
  calc eLpNorm (positiveCap (vi (ns i)) k ⊤) 2 (surfaceMeasure τ)
      = eLpNorm (positiveCap v k ⊤ +
        (fun x => positiveCap (vi (ns i)) k ⊤ x - positiveCap v k ⊤ x)) 2 (surfaceMeasure τ) := by
        rw [← hsum]
    _ ≤ eLpNorm (positiveCap v k ⊤) 2 (surfaceMeasure τ) +
        eLpNorm (fun x => positiveCap (vi (ns i)) k ⊤ x - positiveCap v k ⊤ x) 2
          (surfaceMeasure τ) :=
        eLpNorm_add_le (by norm_num)
    _ ≤ _ := add_le_add le_rfl h2.le

end CoarseDeGiorgi.GoodRadiusEnergy.WideWidth
