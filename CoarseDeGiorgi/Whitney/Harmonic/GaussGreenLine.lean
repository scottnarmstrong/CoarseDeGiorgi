import Homogenization.Sobolev.WeakDerivatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.Rademacher

/-! # Gauss-Green along coordinate lines

The one-dimensional fundamental theorem of calculus for the product of a Lipschitz function and a
smooth function along a line, and the Fubini splitting of `Vec (n + 1)` along one coordinate.
-/

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CoarseDeGiorgi.Whitney.Harmonic

noncomputable section

/-- The fundamental theorem of calculus along the line `t ↦ p + t • e` for the product of a
Lipschitz function `Φ` (differentiable at almost every point of the line) and a differentiable
Lipschitz function `φ`. -/
theorem integral_line_lipschitz_mul_eq_sub {d : ℕ} {K L : ℝ≥0} {Φ φ : Vec d → ℝ}
    (hΦ : LipschitzWith K Φ) (hφL : LipschitzWith L φ) (hφd : Differentiable ℝ φ)
    (p e : Vec d) (a b : ℝ) (hdiff : ∀ᵐ t : ℝ, DifferentiableAt ℝ Φ (p + t • e)) :
    ∫ t in a..b, (Φ (p + t • e) * fderiv ℝ φ (p + t • e) e +
        fderiv ℝ Φ (p + t • e) e * φ (p + t • e)) =
      Φ (p + b • e) * φ (p + b • e) - Φ (p + a • e) * φ (p + a • e) := by
  set γ : ℝ → Vec d := fun t => p + t • e with hγdef
  have hγ : LipschitzWith ‖e‖₊ γ := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    simp only [γ, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      Real.norm_eq_abs, coe_nnnorm]
    rw [mul_comm]
  have hγac : AbsolutelyContinuousOnInterval γ a b :=
    hγ.lipschitzOnWith.absolutelyContinuousOnInterval
  have h1 := hΦ.comp_absolutelyContinuousOnInterval hγac
  have h2 := hφL.comp_absolutelyContinuousOnInterval hγac
  have key := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub h1 h2
  simp only [Function.comp_apply] at key
  rw [← key]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hdiff] with t ht _
  have hγd : HasDerivAt γ e t := by
    have h := ((hasDerivAt_id t).smul_const e).const_add p
    rwa [one_smul] at h
  have hd1 : deriv (Φ ∘ γ) t = fderiv ℝ Φ (γ t) e :=
    (ht.hasFDerivAt.comp_hasDerivAt t hγd).deriv
  have hd2 : deriv (φ ∘ γ) t = fderiv ℝ φ (γ t) e :=
    ((hφd _).hasFDerivAt.comp_hasDerivAt t hγd).deriv
  rw [hd1, hd2]
  ring

variable {n : ℕ}

/-- A point with coordinate `t` inserted at `i` is a translate along `basisVec i`. -/
theorem insertNth_eq_add_smul_basisVec (i : Fin (n + 1)) (t : ℝ) (u : Vec n) :
    (i.insertNth (α := fun _ => ℝ) t u : Vec (n + 1)) =
      i.insertNth (α := fun _ => ℝ) 0 u + t • basisVec i := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp [basisVec_apply]
  · simp [basisVec_apply, Fin.succAbove_ne]

theorem measurePreserving_insertNth (i : Fin (n + 1)) :
    MeasurePreserving (fun z : ℝ × Vec n => i.insertNth (α := fun _ => ℝ) z.1 z.2)
      ((volume : Measure ℝ).prod (volume : Measure (Vec n))) (volume : Measure (Vec (n + 1))) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i).symm

theorem measurableEmbedding_insertNth (i : Fin (n + 1)) :
    MeasurableEmbedding (fun z : ℝ × Vec n => i.insertNth (α := fun _ => ℝ) z.1 z.2) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurableEmbedding

/-- Fubini along the coordinate `i`: the volume integral over `Vec (n + 1)` is the iterated
integral, first in the coordinate `i` and then in the remaining coordinates. -/
theorem integral_eq_integral_insertNth {G : Vec (n + 1) → ℝ} (hG : Integrable G)
    (i : Fin (n + 1)) :
    ∫ x, G x = ∫ u : Vec n, ∫ t : ℝ, G (i.insertNth (α := fun _ => ℝ) t u) := by
  have hmp := measurePreserving_insertNth (n := n) i
  have hint : Integrable (fun z : ℝ × Vec n => G (i.insertNth (α := fun _ => ℝ) z.1 z.2))
      ((volume : Measure ℝ).prod (volume : Measure (Vec n))) :=
    (hmp.integrable_comp_emb (measurableEmbedding_insertNth i)).2 hG
  rw [← hmp.integral_comp (measurableEmbedding_insertNth i) G]
  exact integral_prod_symm _ hint

/-- Almost every point is a point of differentiability on almost every line in the coordinate
direction `i`. -/
theorem ae_ae_differentiableAt_insertNth {K : ℝ≥0} {Φ : Vec (n + 1) → ℝ}
    (hΦ : LipschitzWith K Φ) (i : Fin (n + 1)) :
    ∀ᵐ u : Vec n, ∀ᵐ t : ℝ, DifferentiableAt ℝ Φ (i.insertNth (α := fun _ => ℝ) t u) := by
  have h0 : ∀ᵐ x : Vec (n + 1), DifferentiableAt ℝ Φ x := hΦ.ae_differentiableAt
  have h1 : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure (Vec n))),
      DifferentiableAt ℝ Φ (i.insertNth (α := fun _ => ℝ) z.1 z.2) :=
    (measurePreserving_insertNth i).quasiMeasurePreserving.ae h0
  have h2 : ∀ᵐ w ∂((volume : Measure (Vec n)).prod (volume : Measure ℝ)),
      DifferentiableAt ℝ Φ (i.insertNth (α := fun _ => ℝ) w.2 w.1) :=
    (Measure.measurePreserving_swap).quasiMeasurePreserving.ae h1
  exact Measure.ae_ae_of_ae_prod h2

end

end CoarseDeGiorgi.Whitney.Harmonic
