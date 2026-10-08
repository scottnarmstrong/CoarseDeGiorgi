import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.ChiParam
import CoarseDeGiorgi.Statements.CrossoverExponent
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Harnack.Final.CrossoverRestriction
import CoarseDeGiorgi.Harnack.CrossoverFinal.Parameters
import CoarseDeGiorgi.Harnack.WeakHarnack.EpsilonLimit
import CoarseDeGiorgi.Harnack.CrossoverFinal.EnnrealAverage
import CoarseDeGiorgi.Harnack.CrossoverFinal.PowerIntegrability
import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Final

private theorem originCube_subset_of_radii {d : ℕ} {r R : ℝ}
    (hrR : r ≤ R) : originCube (d := d) r ⊆ originCube R := by
  intro x hx i
  dsimp [originCube] at hx ⊢
  constructor <;> linarith [hx i]

/-- Restrict `l.crossover`'s crossover exponent by Hölder to the iteration range,
then convert its bound to the real-average input of the weak-Harnack assembly.
Shifted-power integrability is supplied by the signed-power estimates. -/
theorem crossover_average_of_statement_crossover
    (hCrossover : ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ c : ℝ, 0 < c ∧
        c ≤ paramR q / 4 ∧
        ∃ C : ℝ≥0∞, C < ⊤ ∧
          ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
            spatialMomentRange a ha p q s t →
            ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
              (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
              IsWeightedSupersolution a (originCube 1) u G →
              ∀ ε : ℝ, 0 < ε →
                let b := crossoverExponent c a ha s t p q hs ht
                  (le_of_lt hp) (le_of_lt hq)
                ((volume (originCube (d := d) (3 / 4)))⁻¹ *
                    ∫⁻ x in originCube (3 / 4), ENNReal.ofReal ((u x + ε) ^ b)) *
                  ((volume (originCube (d := d) (3 / 4)))⁻¹ *
                    ∫⁻ x in originCube (3 / 4),
                      ENNReal.ofReal ((u x + ε) ^ (-b))) ≤ C)
    {d : ℕ} (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ c : ℝ, 0 < c ∧
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) ∧
      ∃ Kcross : ℝ, 0 ≤ Kcross ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSupersolution a (originCube 1) u G →
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            ∀ ε : ℝ, 0 < ε →
              let b := crossoverExponent c a ha s t p q hs ht hp.le hq.le
              volumeAverage (originCube (3 / 4)) (fun x => (u x + ε) ^ b) *
                volumeAverage (originCube (3 / 4))
                  (fun x => (u x + ε) ^ (-b)) ≤ Kcross := by
  obtain ⟨c₀, hc₀, _, C₀, hC₀top, hCrossoverBound⟩ :=
    hCrossover d hd p q s t hp hq hs ht hθ
  have hχ := Harnack.CrossoverFinal.chiParam_gt_one_of_source_parameters
    hd p q s t hp hq hs ht hθ
  have hr : 0 < paramR q := by
    unfold paramR
    exact div_pos (by linarith only [hq]) (by linarith only [hq])
  let c := min c₀ (min (1 / 2) (paramR q / (16 * chiParam d q t)))
  have hc : 0 < c := lt_min hc₀ (lt_min (by norm_num) (by positivity))
  have hcRange : c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) := min_le_right _ _
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  let C := max C₀ 1
  have hCtop : C < ⊤ := max_lt hC₀top ENNReal.one_lt_top
  refine ⟨c, hc, hcRange, C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a ha hrange u G hsuper hnonneg ε hε
  let V : Set (Vec d) := originCube (d := d) (3 / 4)
  let b : ℝ := crossoverExponent c a ha s t p q hs ht hp.le hq.le
  let f : Vec d → ℝ := fun x => (u x + ε) ^ b
  let g : Vec d → ℝ := fun x => (u x + ε) ^ (-b)
  have hsmall : V ⊆ originCube (d := d) 1 :=
    originCube_subset_of_radii (by norm_num)
  have hnonnegSmall : 0 ≤ᵐ[volume.restrict V] u := by
    exact ae_restrict_of_ae_restrict_of_subset hsmall hnonneg
  have hshiftPos : ∀ᵐ x ∂(volume.restrict V), 0 < u x + ε := by
    filter_upwards [hnonnegSmall] with x hx
    exact add_pos_of_nonneg_of_pos hx hε
  have hfnonneg : 0 ≤ᵐ[volume.restrict V] f := by
    filter_upwards [hshiftPos] with x hx
    dsimp [f]
    exact Real.rpow_nonneg hx.le b
  have hgnonneg : 0 ≤ᵐ[volume.restrict V] g := by
    filter_upwards [hshiftPos] with x hx
    dsimp [g]
    exact Real.rpow_nonneg hx.le (-b)
  have hpower := Harnack.CrossoverFinal.shifted_signed_powers_integrable_of_supersolution
    hd p q s t hp hq hs ht hθ a ha hrange c hc hcRange u G hnonneg hsuper ε hε
  dsimp only at hpower
  rcases hpower with ⟨hplus, hminus⟩
  have hVsubset : V ⊆ originCube (d := d) (7 / 8) :=
    originCube_subset_of_radii (by norm_num)
  have hfint : IntegrableOn f V := by
    dsimp [f, b, V]
    exact hplus.mono_set hVsubset
  have hgint : IntegrableOn g V := by
    dsimp [g, b, V]
    exact hminus.mono_set hVsubset
  have hVpos : 0 < volume V := by
    dsimp [V]
    exact Harnack.Scalar.volume_originCube_pos (by norm_num)
  have hVtop : volume V < ⊤ := by
    dsimp [V]
    exact lt_of_le_of_lt (Harnack.Scalar.volume_originCube_le_one (by norm_num))
      ENNReal.one_lt_top
  have hfavg : 0 ≤ volumeAverage V f := by
    rw [Homogenization.volumeAverage]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg_of_ae hfnonneg)
  have hfENN := Harnack.CrossoverFinal.ennrealAverage_eq_ofReal_volumeAverage
    V hVtop hVpos f hfint hfnonneg
  have hgENN := Harnack.CrossoverFinal.ennrealAverage_eq_ofReal_volumeAverage
    V hVtop hVpos g hgint hgnonneg
  have huMeas : AEStronglyMeasurable u (volume.restrict (originCube 1)) := by
    have h := hsuper.1.1.neg
    convert h using 1 <;> first | rfl | (funext x; exact (neg_neg (u x)).symm)
  have hwMeas : AEStronglyMeasurable (fun x => u x + ε) (volume.restrict V) :=
    (huMeas.mono_measure (Measure.restrict_mono hsmall le_rfl)).add
      aestronglyMeasurable_const
  have hΘtop := Harnack.Crossover.contrast_lt_top_of_spatialMomentRange
    a ha s t p q hs ht hp.le hq.le hrange
  have hb : 0 < b := Harnack.WeakHarnack.crossoverExponent_pos
    c hc a ha s t p q hs ht hp.le hq.le hΘtop
  have hbb₀ : b ≤ crossoverExponent c₀ a ha s t p q hs ht hp.le hq.le :=
    mul_le_mul_of_nonneg_right hcc₀ ENNReal.toReal_nonneg
  have hraw := crossover_signed_product_le_of_exponent_le V (fun x => u x + ε)
    hb hbb₀ hwMeas hshiftPos hVpos hVtop.ne
    (hCrossoverBound a ha hrange u G hnonneg hsuper ε hε)
  have hrawV :
      ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x)) *
        ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (g x)) ≤ C := by
    simpa only [V, f, g, b] using hraw
  have hfENN' :
      (volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x) =
        ENNReal.ofReal (volumeAverage V f) := hfENN
  have hgENN' :
      (volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (g x) =
        ENNReal.ofReal (volumeAverage V g) := hgENN
  rw [hfENN', hgENN'] at hrawV
  have hproductENN :
      ENNReal.ofReal (volumeAverage V f) * ENNReal.ofReal (volumeAverage V g) =
        ENNReal.ofReal (volumeAverage V f * volumeAverage V g) :=
    (ENNReal.ofReal_mul hfavg).symm
  rw [hproductENN] at hrawV
  have hCeq : C = ENNReal.ofReal C.toReal :=
    (ENNReal.ofReal_toReal hCtop.ne).symm
  rw [hCeq] at hrawV
  have hreal := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hrawV
  change volumeAverage V f * volumeAverage V g ≤ C.toReal
  exact hreal

end CoarseDeGiorgi.Harnack.Final
