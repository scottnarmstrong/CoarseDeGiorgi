module

public import CoarseDeGiorgi.Weighted.GradientRepresentation
public import CoarseDeGiorgi.Weighted.Energy
public import CoarseDeGiorgi.Harnack.Selection.Cap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerLimits

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Energy convergence of smooth gradients implies convergence of their pairing
with a fixed finite-energy gradient. This is the interior pairing limit for
the signed-power tests.
-/
theorem weighted_pairing_tendsto_of_energy_approximation
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn V a)
    {F : ℕ → Vec d → Vec d} {K H : Vec d → Vec d}
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (hKmeas : AEStronglyMeasurable K (volume.restrict V))
    (hHmeas : AEStronglyMeasurable H (volume.restrict V))
    (hFE : ∀ n, CoarseDeGiorgi.weightedEnergy a V (F n) < ⊤)
    (hKE : CoarseDeGiorgi.weightedEnergy a V K < ⊤)
    (hHE : CoarseDeGiorgi.weightedEnergy a V H < ⊤)
    (hFK : Tendsto (fun n => CoarseDeGiorgi.weightedEnergy a V (F n - K))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in V, vecDot (F n x) (matVecMul (a x) (H x)))
      atTop (𝓝 (∫ x in V, vecDot (K x) (matVecMul (a x) (H x)))) := by
  let Fc : ℕ → Weighted.GradientCore ha := fun n =>
    ⟨F n, hFmeas n, Weighted.quadratic_integrable ha (hFmeas n) (hFE n)⟩
  let Kc : Weighted.GradientCore ha :=
    ⟨K, hKmeas, Weighted.quadratic_integrable ha hKmeas hKE⟩
  let Hc : Weighted.GradientCore ha :=
    ⟨H, hHmeas, Weighted.quadratic_integrable ha hHmeas hHE⟩
  have hFK' : Tendsto
      (fun n => CoarseDeGiorgi.weightedEnergy a V ((Fc n).field - Kc.field))
      atTop (𝓝 0) := by
    simpa only [Fc, Kc, Weighted.GradientCore.field] using hFK
  have hFc : Tendsto (fun n => (Fc n : Weighted.GradientHilbert ha)) atTop
      (𝓝 (Kc : Weighted.GradientHilbert ha)) :=
    Weighted.GradientCore.tendsto_coe_of_energy ha hFK'
  have hInner := hFc.inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := (Hc : Weighted.GradientHilbert ha)))
  have hInnerF (n : ℕ) :
      inner ℝ (Fc n : Weighted.GradientHilbert ha) (Hc : Weighted.GradientHilbert ha) =
        ∫ x in V, vecDot (F n x) (matVecMul (a x) (H x)) := by
    rw [Weighted.gradientHilbert_inner_coe]
    rfl
  have hInnerK :
      inner ℝ (Kc : Weighted.GradientHilbert ha) (Hc : Weighted.GradientHilbert ha) =
        ∫ x in V, vecDot (K x) (matVecMul (a x) (H x)) := by
    rw [Weighted.gradientHilbert_inner_coe]
    rfl
  have hLeft : (fun n =>
      inner ℝ (Fc n : Weighted.GradientHilbert ha) (Hc : Weighted.GradientHilbert ha)) =
      (fun n => ∫ x in V, vecDot (F n x) (matVecMul (a x) (H x))) := by
    funext n
    exact hInnerF n
  have hRight : inner ℝ (Kc : Weighted.GradientHilbert ha)
      (Hc : Weighted.GradientHilbert ha) =
      ∫ x in V, vecDot (K x) (matVecMul (a x) (H x)) := hInnerK
  rw [hLeft, hRight] at hInner
  exact hInner

/-- For a finite positive cap, the limiting quotient density dominates the energy
of the capped gradient. Above the cap the quotient may contribute a positive
tail, so equality is not asserted.
-/
theorem positive_cap_ratio_dominates_energy
    (hV : IsOpen V) (ha : CoarseDeGiorgi.IsWeightedCoeffOn V a)
    {v : Vec d → ℝ} {G : Vec d → Vec d} {N : ℝ≥0∞}
    (hcap : CoarseDeGiorgi.MemH1a a V
      (Selection.selectionCap 0 N v)
      (Selection.selectionCapGradient 0 N v G))
    (hpositive : ∀ᵐ x ∂volume.restrict V, 0 < v x)
    (hNtop : N ≠ ⊤)
    (hRatio : IntegrableOn (fun x =>
      (Selection.selectionCap 0 N v x / v x) *
        vecDot (G x) (matVecMul (a x) (G x))) V) :
    (CoarseDeGiorgi.weightedEnergy a V
      (Selection.selectionCapGradient 0 N v G)).toReal ≤
      ∫ x in V, (Selection.selectionCap 0 N v x / v x) *
        vecDot (G x) (matVecMul (a x) (G x)) := by
  have hE := Weighted.MemH1a.energy_lt_top hV ha hcap
  have hquadCap := Weighted.quadratic_integrable ha hcap.2.1 hE
  have hqnonneg := Weighted.quadratic_nonneg ha G
  have hpoint : ∀ᵐ x ∂volume.restrict V,
      vecDot (Selection.selectionCapGradient 0 N v G x)
        (matVecMul (a x) (Selection.selectionCapGradient 0 N v G x)) ≤
      (Selection.selectionCap 0 N v x / v x) *
        vecDot (G x) (matVecMul (a x) (G x)) := by
    filter_upwards [hpositive, hqnonneg] with x hx hq
    have hcapNonneg : 0 ≤ Selection.selectionCap 0 N v x := by
      simp [Selection.selectionCap, hNtop]
    have hratioNonneg : 0 ≤
        (Selection.selectionCap 0 N v x / v x) *
          vecDot (G x) (matVecMul (a x) (G x)) :=
      mul_nonneg (div_nonneg hcapNonneg hx.le) hq
    by_cases hband : 0 < v x ∧ v x < N.toReal
    · have hgrad : Selection.selectionCapGradient 0 N v G x = G x := by
        simp [Selection.selectionCapGradient, hNtop, hband]
      have hvalue : Selection.selectionCap 0 N v x = v x := by
        simp [Selection.selectionCap, hNtop, max_eq_left hx.le,
          min_eq_left hband.2.le]
      rw [hgrad, hvalue, div_self hx.ne']
      simp
    · have hgrad : Selection.selectionCapGradient 0 N v G x = 0 := by
        simp [Selection.selectionCapGradient, hNtop, hband]
      rw [hgrad, matVecMul_zero, vecDot_zero_left]
      exact hratioNonneg
  have hineq := integral_mono_ae hquadCap hRatio hpoint
  rw [← Weighted.energy_toReal ha hcap.2.1] at hineq
  exact hineq

end CoarseDeGiorgi.Harnack.PowerLimits
