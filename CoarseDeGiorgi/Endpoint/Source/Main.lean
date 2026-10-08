module

public import CoarseDeGiorgi.Endpoint.Source.Measure
public import CoarseDeGiorgi.Endpoint.Source.Solution
public import CoarseDeGiorgi.Endpoint.Source.Geometry
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.MemH1a0
public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.SmoothGrad
public import CoarseDeGiorgi.Statements.OriginCube

/-! `l.source.mass`, Steps 1-2: the source measure of a supersolution and the potential of its
restriction to `(3/4)□₀`. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint

/-- `l.source.mass`, Step 1: the source measure `μ = -∇·a∇u` of a supersolution on `□₀`. -/
theorem source_measure_exists {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hs : IsWeightedSupersolution a (originCube 1) u G) :
    ∃ μ : Measure (Vec d),
      μ (originCube 1)ᶜ = 0 ∧
      (∀ K : Set (Vec d), IsCompact K → K ⊆ originCube 1 → μ K < ⊤) ∧
      (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ originCube 1 →
          ∫ x, φ x ∂μ =
            ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ∂volume) :=
  exists_flux_measure (originCube_domain one_pos) (originCube_nonempty one_pos) ha hs

theorem ofReal_sqrt_toReal_eq_rpow {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    ENNReal.ofReal (Real.sqrt x.toReal) = x.rpow (1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hx]
  rfl

/-- `l.source.mass`, Steps 1-2: for any source measure `μ` of the nonnegative supersolution `u`, the
restriction `ν` of `μ` to `(3/4)□₀` is a finite measure satisfying the continuity hypothesis of
`p.endpoint.potential`, its potential `V` satisfies `0 ≤ V ≤ u`, `u - V` is a solution in `(3/4)□₀`, and
`V` is a solution in every bounded convex domain in `□₀ \ closure ((3/4)□₀)`. -/
theorem source_potential {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu0 : ∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x)
    (hs : IsWeightedSupersolution a (originCube 1) u G)
    (μ : Measure (Vec d)) (hμ0 : μ (originCube 1)ᶜ = 0)
    (hμK : ∀ K : Set (Vec d), IsCompact K → K ⊆ originCube 1 → μ K < ⊤)
    (hμ : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ originCube 1 →
      ∫ x, φ x ∂μ = ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ∂volume)
    (ν : Measure (Vec d)) (hν : ν = μ.restrict (originCube (3 / 4))) :
    IsFiniteMeasure ν ∧ ν (originCube 1)ᶜ = 0 ∧
    (∃ M : ℝ, 0 ≤ M ∧
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ originCube 1 →
        ENNReal.ofReal |∫ x, φ x ∂ν| ≤
          ENNReal.ofReal M *
            (weightedEnergy a (originCube 1) (smoothGrad φ)).rpow (1 / 2)) ∧
    ∃ (V : Vec d → ℝ) (Gv : Vec d → Vec d),
      MemH1a0 a (originCube 1) V Gv ∧
      (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ originCube 1 →
          ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume =
            ∫ x, φ x ∂ν) ∧
      (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ V x) ∧
      (∀ᵐ x ∂(volume.restrict (originCube 1)), V x ≤ u x) ∧
      IsWeightedSolution a (originCube (3 / 4)) (fun x => u x - V x) (fun x => G x - Gv x) ∧
      (∀ Q : Set (Vec d), IsOpenBoundedConvexDomain Q →
        Q ⊆ originCube 1 \ closure (originCube (3 / 4)) → IsWeightedSolution a Q V Gv) := by
  have hV := originCube_domain (d := d) one_pos
  have hne := originCube_nonempty (d := d) (one_pos : (0 : ℝ) < 1)
  have hW := originCube_domain (d := d) (by norm_num : (0 : ℝ) < 3 / 4)
  have hWV : originCube (d := d) (3 / 4) ⊆ originCube 1 :=
    originCube_mono' (by norm_num) one_pos (by norm_num)
  have hcl : closure (originCube (d := d) (3 / 4)) ⊆ originCube 1 :=
    closure_originCube_subset (by norm_num) one_pos (by norm_num)
  have hmem := supersolution_memH1a hV hne ha hs
  have hG := hmem.2.1
  have hEG := Weighted.MemH1a.energy_lt_top hV.isOpen ha hmem
  have hfin : IsFiniteMeasure ν := ⟨by
    rw [hν, Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt
      (hμK _ (isCompact_closure_originCube (by norm_num)) hcl)⟩
  have hνle : ν ≤ μ := hν ▸ Measure.restrict_le_self
  have hνV : ν (originCube 1)ᶜ = 0 := le_antisymm ((hνle _).trans hμ0.le) (zero_le)
  have hrepF : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ originCube 1 → ∫ x, φ x ∂μ = fluxPairing a (originCube 1) G φ :=
    fun φ h1 h2 h3 => hμ φ h1 h2 h3
  have hEφ : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      weightedEnergy a (originCube 1) (smoothGrad φ) < ⊤ :=
    fun φ h1 h2 => (Weighted.isSmoothCore_of_supported ha h1 h2).2.2
  have hbd : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ originCube 1 → |∫ x, φ x ∂ν| ≤
        Real.sqrt (weightedEnergy a (originCube 1) G).toReal *
          Real.sqrt (weightedEnergy a (originCube 1) (smoothGrad φ)).toReal := by
    intro φ hφ hc hts
    have hint : Integrable (fun x => |φ x|) μ :=
      integrable_of_supported hμK hc hts hφ.continuous.abs
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, abs_zero])
    calc |∫ x, φ x ∂ν| = ‖∫ x, φ x ∂ν‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, ‖φ x‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ x, |φ x| ∂μ := by
        simp only [Real.norm_eq_abs]
        exact integral_mono_measure hνle (ae_of_all _ fun x => abs_nonneg _) hint
      _ ≤ _ := by
        rw [mul_comm]
        exact integral_abs_le hV.isOpen ha hG hEG hμK hrepF hφ hc hts
  refine ⟨hfin, hνV, ⟨Real.sqrt (weightedEnergy a (originCube 1) G).toReal, Real.sqrt_nonneg _, ?_⟩, ?_⟩
  · intro φ hφ hc hts
    calc ENNReal.ofReal |∫ x, φ x ∂ν|
        ≤ ENNReal.ofReal (Real.sqrt (weightedEnergy a (originCube 1) G).toReal *
          Real.sqrt (weightedEnergy a (originCube 1) (smoothGrad φ)).toReal) :=
          ENNReal.ofReal_le_ofReal (hbd φ hφ hc hts)
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
          ofReal_sqrt_toReal_eq_rpow (hEφ φ hφ hc).ne]
  obtain ⟨v, Gv, hv, heq⟩ := exists_potential hV hne ha (ν := ν)
    (M := Real.sqrt (weightedEnergy a (originCube 1) G).toReal) hbd
  have hvH := Weighted.MemH1a0.memH1a ha hv
  have hEGv := Weighted.MemH1a.energy_lt_top hV.isOpen ha hvH
  have hP : PotentialData a (originCube 1) μ ν G Gv :=
    ⟨hνle, hμK, hG, hEG, hv.2.1, hEGv, hrepF, heq⟩
  have hνφ : ∀ φ : Vec d → ℝ, tsupport φ ⊆ originCube (3 / 4) →
      ∫ x, φ x ∂ν = ∫ x, φ x ∂μ := by
    intro φ hts
    rw [hν]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hts h)
  refine ⟨v, Gv, hv, heq, potential_nonneg hV hne ha hP hv, potential_le hV hne ha hP hv hmem hu0,
    ?_, ?_⟩
  · refine isWeightedSolution_of_vanishing hV hne ha hW hWV (w := fun x => u x - v x)
      (X := fun x => G x - Gv x) (Weighted.MemH1a.sub hV hne ha hmem hvH) ?_
    intro φ hφ hc hts
    have hts' := hts.trans hWV
    have i1 := fluxPairing_integrable hV.isOpen ha hG hEG hφ hc hts'
    have i2 := fluxPairing_integrable hV.isOpen ha hv.2.1 hEGv hφ hc hts'
    unfold fluxPairing
    have hpt : ∀ x, vecDot (smoothGrad φ x) (matVecMul (a x) (G x - Gv x)) =
        vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) -
          vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) := by
      intro x
      simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_neg_right]
    simp only [hpt]
    rw [integral_sub i1 i2, ← hμ φ hφ hc hts', heq φ hφ hc hts', hνφ φ hts, sub_self]
  · intro Q hQ hQsub
    have hQV : Q ⊆ originCube 1 := fun x hx => (hQsub hx).1
    refine isWeightedSolution_of_vanishing hV hne ha hQ hQV hvH ?_
    intro φ hφ hc hts
    change ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume = 0
    rw [heq φ hφ hc (hts.trans hQV), hν]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => (hQsub (hts h)).2 (subset_closure hx)

end CoarseDeGiorgi.Endpoint
