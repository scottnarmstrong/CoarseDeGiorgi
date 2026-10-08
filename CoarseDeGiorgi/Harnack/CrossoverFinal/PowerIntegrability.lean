import CoarseDeGiorgi.Assembly.HybridFractional
import CoarseDeGiorgi.Harnack.Iterations.ExponentRange
import CoarseDeGiorgi.Harnack.Powers.SignedPower
import CoarseDeGiorgi.Harnack.Crossover.Normalization
import CoarseDeGiorgi.Harnack.CrossoverFinal.Parameters
import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ChiParam

namespace CoarseDeGiorgi.Harnack.CrossoverFinal

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

private theorem memLp_integrable_of_finite_measure {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {r : ℝ≥0∞}
    (hμ : IsFiniteMeasure μ) (hmem : MemLp f r μ) (hr : 1 ≤ r) :
    Integrable f μ :=
  @MemLp.integrable α ℝ _ μ _ _ r hr f hμ hmem

/-- Supersolution membership and the power statement of Lemma `l.weighted.testing` imply the
integrability needed to normalize both signed powers on the seven-eighths cube. -/
theorem shifted_signed_powers_integrable_of_supersolution {d : ℕ}
    (hd : 3 ≤ d) (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hs : 0 < s) (ht : 0 < t) (hθ : 0 < paramTheta d p q s t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t)
    (c : ℝ) (hc : 0 < c)
    (hcRange : c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)))
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hnonneg : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), 0 ≤ u x)
    (hu : IsWeightedSupersolution a (originCube (d := d) 1) u G)
    (ε : ℝ) (hε : 0 < ε) :
    let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
    IntegrableOn (fun x => (u x + ε) ^ pC) (originCube (d := d) (7 / 8)) ∧
      IntegrableOn (fun x => (u x + ε) ^ (-pC)) (originCube (d := d) (7 / 8)) := by
  let θ := contrast a ha s t p q hs ht hp.le hq.le
  have hθtop : θ < ⊤ := by
    dsimp [θ]
    exact Harnack.Crossover.contrast_lt_top_of_spatialMomentRange
      a ha s t p q hs ht hp.le hq.le hrange
  have hθge : 1 ≤ θ := by
    dsimp [θ]
    exact contrast_ge_one_of_spatialMomentRange hd a ha p q s t hp hq hs ht hrange
  let r := paramR q
  have hr1 : 1 < r := by
    dsimp [r, paramR]
    rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  have hr2 : r < 2 := by
    dsimp [r, paramR]
    rw [div_lt_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  have hExponent := Harnack.Iterations.ruled_exponent_range_of_moment_comparison
    hd p q s t hp hq hs ht hθ a ha ⟨hθge, hθtop⟩ c hc (by
      simpa [chiParam] using hcRange)
  have hpCpos : 0 < crossoverExponent c a ha s t p q hs ht hp.le hq.le := by
    simpa only [show crossoverExponent c a ha s t p q hs ht hp.le hq.le =
      c * ((1 + θ).rpow (-(1 / 2 : ℝ))).toReal by rfl] using hExponent.1
  have hpCle : crossoverExponent c a ha s t p q hs ht hp.le hq.le ≤ c := hExponent.2.1
  have hpCsmall : crossoverExponent c a ha s t p q hs ht hp.le hq.le < 1 / 2 := by
    have hstar : crossoverExponent c a ha s t p q hs ht hp.le hq.le <
        paramR q / 4 := by
      simpa only [CoarseDeGiorgi.crossoverExponent] using hExponent.2.2.1
    have hstar' : paramR q / 4 < 2 / 4 :=
      div_lt_div_of_pos_right hr2 (by norm_num)
    norm_num at hstar'
    exact lt_trans hstar hstar'
  have hunit := Assembly.hybrid_unitCube_domain (d := d)
  have hne : NeZero d := ⟨by omega⟩
  change IsWeightedSubsolution a (originCube (d := d) 1) (-u) (-G) at hu
  have huMem : MemH1a a (originCube (d := d) 1) u G := by
    have h := Weighted.MemH1a.neg hunit.1 hunit.2 ha hu.1
    simpa only [Pi.neg_apply, neg_neg] using h
  have hpCne : crossoverExponent c a ha s t p q hs ht hp.le hq.le ≠ 0 :=
    ne_of_gt hpCpos
  have hnegSmall : -crossoverExponent c a ha s t p q hs ht hp.le hq.le < 1 / 2 := by
    linarith
  have hpackagePos := @Harnack.Powers.signedPower_source_package d hne
    (originCube (d := d) 1) a hunit.1 hunit.2 ha u G huMem hu hnonneg ε
    (crossoverExponent c a ha s t p q hs ht hp.le hq.le) r hε hpCsmall hpCne hr1 hr2
  have hpackageNeg := @Harnack.Powers.signedPower_source_package d hne
    (originCube (d := d) 1) a hunit.1 hunit.2 ha u G huMem hu hnonneg ε
    (-crossoverExponent c a ha s t p q hs ht hp.le hq.le) r hε hnegSmall
    (neg_ne_zero.mpr hpCne) hr1 hr2
  let V := originCube (d := d) (7 / 8)
  have hsubset : V ⊆ originCube (d := d) 1 :=
    Harnack.Scalar.originCube_subset_of_le_one (by norm_num)
  have hμ : volume.restrict V ≤ volume.restrict (originCube (d := d) 1) :=
    Measure.restrict_mono hsubset le_rfl
  have hfinite : volume V < ⊤ := by
    exact lt_of_le_of_lt
      (Harnack.Scalar.volume_originCube_le_one (d := d) (by norm_num))
      ENNReal.one_lt_top
  have hfiniteMeasure : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hfinite
  have hrEN : 1 ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr1.le
  constructor
  · change Integrable (fun x => (u x + ε) ^
      crossoverExponent c a ha s t p q hs ht hp.le hq.le) (volume.restrict V)
    exact memLp_integrable_of_finite_measure hfiniteMeasure
      (hpackagePos.2.1.mono_measure hμ) hrEN
  · change Integrable (fun x => (u x + ε) ^
      (-crossoverExponent c a ha s t p q hs ht hp.le hq.le)) (volume.restrict V)
    exact memLp_integrable_of_finite_measure hfiniteMeasure
      (hpackageNeg.2.1.mono_measure hμ) hrEN

end

end CoarseDeGiorgi.Harnack.CrossoverFinal
