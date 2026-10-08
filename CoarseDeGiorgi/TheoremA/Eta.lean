module

public import CoarseDeGiorgi.TheoremA.Endpoint
public import CoarseDeGiorgi.Harnack.Moments.MomentComparison
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.LocallyBoundedAbove
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.UpperMoment

/-! Corollary B (with the power `Θ ^ ((d-1)/(2ηθ))`) from the Theorem A estimate: interpolation
and the radius iteration (hole filling) in `Weighted.testing_lr_bound_of_l2`. -/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.TheoremA

theorem corollaryB_of_theoremA (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) {γ : ℝ} (hγ : 0 < γ) {C_A : ℝ≥0∞} (hCA : C_A < ⊤)
    (hA : ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          LocallyBoundedAbove (originCube 1) u ∧
          ∀ ρ R : ℝ, (1 / 2 : ℝ) ≤ ρ → ρ < R → R ≤ 1 →
            eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
              C_A * (ENNReal.ofReal (R - ρ)).rpow (-γ) *
                (contrast a ha s t p q hs ht hp.le hq.le).rpow
                  (((d : ℝ) - 1) / (4 * paramTheta d p q s t)) *
                eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) ∧
            (R < 1 → eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) < ⊤)) :
    ∀ η : ℝ, 0 < η → η < 2 →
      ∃ C_η : ℝ≥0∞, C_η < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSubsolution a (originCube 1) u G →
            LocallyBoundedAbove (originCube 1) u ∧
            ∀ ρ R : ℝ, (1 / 2 : ℝ) ≤ ρ → ρ < R → R ≤ 1 →
              eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
                C_η * (ENNReal.ofReal (R - ρ)).rpow (-2 * γ / η) *
                  (contrast a ha s t p q hs ht hp.le hq.le).rpow
                    (((d : ℝ) - 1) / (2 * η * paramTheta d p q s t)) *
                  eLpNorm (positivePart u) (ENNReal.ofReal η)
                    (volume.restrict (originCube R)) ∧
              (R < 1 → eLpNorm (positivePart u) (ENNReal.ofReal η)
                (volume.restrict (originCube R)) < ⊤) := by
  intro η hη hη2
  have hμ : Monotone (fun r : ℝ => volume.restrict (originCube (d := d) r)) := by
    intro r r' hrr'
    exact Measure.restrict_mono (originCube_mono hrr') le_rfl
  obtain ⟨K, hK, hupgrade⟩ :=
    Weighted.testing_lr_bound_of_l2 hμ hCA hγ hη hη2
  let C_η : ℝ≥0∞ := K + 1
  have hCηtop : C_η < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hK, ENNReal.one_lt_top⟩
  have hCηpos : 0 < C_η := lt_of_lt_of_le zero_lt_one (le_add_left le_rfl)
  have hKCη : K ≤ C_η := by dsimp [C_η]; exact le_add_right le_rfl
  refine ⟨C_η, hCηtop, ?_⟩
  intro a ha hupper hlower u G hsub
  obtain ⟨hlocal, hold⟩ := hA a ha hupper hlower u G hsub
  refine ⟨hlocal, ?_⟩
  intro ρ R hρ hρR hR
  let B : ℝ≥0∞ := contrast a ha s t p q hs ht hp.le hq.le
  let b : ℝ := ((d : ℝ) - 1) / (4 * paramTheta d p q s t)
  let β : ℝ := 2 * b / η
  let α : ℝ := -2 * γ / η
  have hbpos : 0 < b := by
    dsimp [b]
    apply div_pos
    · have hdi : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
      linarith
    · exact mul_pos (by norm_num) hθ
  have hβeq : β = ((d : ℝ) - 1) / (2 * η * paramTheta d p q s t) := by
    dsimp [β, b]
    ring
  have hβnonneg : 0 ≤ β := by
    rw [hβeq]
    apply div_nonneg
    · have hdi : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
      linarith
    · positivity
  have hcontrast : contrast a ha s t p q hs ht hp.le hq.le < ⊤ :=
    ENNReal.div_lt_top hupper.ne hlower.ne'
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one
    (Harnack.Moments.moment_contrast_ge_one (by omega) a ha hs ht hp.le hq.le hupper hlower)
  have hBtop : B < ⊤ := hcontrast
  have huMeas : AEStronglyMeasurable u (volume.restrict (originCube 1)) := hsub.1.1
  have hfMeas (r : ℝ) (hr : r ≤ 1) :
      AEStronglyMeasurable (positivePart u) (volume.restrict (originCube r)) := by
    exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
      (huMeas.mono_measure (Measure.restrict_mono (originCube_mono hr) le_rfl))
  have hAall : ∀ ρ' R' : ℝ, ρ ≤ ρ' → ρ' < R' → R' ≤ 1 →
      eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ')) ≤
        C_A * (ENNReal.ofReal (R' - ρ')) ^ (-γ) * B ^ b *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube R')) := by
    intro ρ' R' hρ' hρ'R' hR'
    have hA := (hold ρ' R' (hρ.trans hρ') hρ'R' hR').1
    simpa only [B, b, ENNReal.rpow_eq_pow] using hA
  have hηboundAt (R' : ℝ) (hρR' : ρ < R') (hR' : R' < 1) :
      eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
        C_η * (ENNReal.ofReal (R' - ρ)).rpow α * B.rpow β *
          eLpNorm (positivePart u) (ENNReal.ofReal η)
            (volume.restrict (originCube R')) := by
    have hM : eLpNorm (positivePart u) ⊤
        (volume.restrict (originCube R')) < ⊤ :=
      Assembly.theoremA_inner_norm_finite huMeas hlocal hR' ⊤
    have hN : eLpNorm (positivePart u) (ENNReal.ofReal η)
        (volume.restrict (originCube R')) < ⊤ :=
      Assembly.theoremA_inner_norm_finite huMeas hlocal hR' (ENNReal.ofReal η)
    have hupgradeBound := hupgrade (positivePart u) B b hBpos hBtop ρ R'
      hρR' hM hN (hfMeas R' hR'.le) (by
        intro ρ'' R'' hρ'' hρ''R'' hR''
        exact hAall ρ'' R'' hρ'' hρ''R'' (hR''.trans hR'.le))
    have hupgradeNorm :
        eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
          K * (ENNReal.ofReal (R' - ρ)).rpow α * B.rpow β *
            eLpNorm (positivePart u) (ENNReal.ofReal η)
              (volume.restrict (originCube R')) := by
      simpa only [ENNReal.rpow_eq_pow, α, β, hβeq] using hupgradeBound
    calc
      _ ≤ K * (ENNReal.ofReal (R' - ρ)).rpow α * B.rpow β *
            eLpNorm (positivePart u) (ENNReal.ofReal η)
              (volume.restrict (originCube R')) := hupgradeNorm
      _ ≤ C_η * (ENNReal.ofReal (R' - ρ)).rpow α * B.rpow β *
            eLpNorm (positivePart u) (ENNReal.ofReal η)
              (volume.restrict (originCube R')) := by
        gcongr
  by_cases hRlt : R < 1
  · have hηbound := hηboundAt R hρR hRlt
    have hN : eLpNorm (positivePart u) (ENNReal.ofReal η)
        (volume.restrict (originCube R)) < ⊤ :=
      Assembly.theoremA_inner_norm_finite huMeas hlocal hRlt (ENNReal.ofReal η)
    refine ⟨?_, ?_⟩
    · simpa only [α, β, ENNReal.rpow_eq_pow, B, hβeq] using hηbound
    · intro _
      exact hN
  · have hReq : R = 1 := le_antisymm hR (le_of_not_gt hRlt)
    have hρ1 : ρ < 1 := by simpa [hReq] using hρR
    have hηend := eta_endpoint_of_interior hρ1 hη hβnonneg
      hBpos hBtop hCηpos hCηtop (hfMeas 1 le_rfl) (by
        intro R' hρR' hR'lt
        exact hηboundAt R' hρR' hR'lt)
    refine ⟨?_, ?_⟩
    · simpa [hReq, α, β, ENNReal.rpow_eq_pow, B, hβeq] using hηend
    · intro hRlt'
      rw [hReq] at hRlt'
      exact (lt_irrefl (1 : ℝ) hRlt').elim

end CoarseDeGiorgi.TheoremA
