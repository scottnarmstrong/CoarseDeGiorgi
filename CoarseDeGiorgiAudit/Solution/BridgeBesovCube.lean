module

public import CoarseDeGiorgi.Statements.MomentBoundsBesov
public import CoarseDeGiorgi.Statements.ParamTheta

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.Solution.BridgeBesovCube

/-- From finite cube quasi-norms (Theorem D(ii)): the moment hypotheses of the main results hold
and the contrast is bounded by `(d!)² N_a N_{a⁻¹}`. -/
theorem moment_data (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (hA : ∀ i j, Integrable (fun x => a x i j)
      (volume.restrict (CoarseDeGiorgi.originCube 1)))
    (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j)
      (volume.restrict (CoarseDeGiorgi.originCube 1)))
    (hap : CoarseDeGiorgi.besovCubeNorm a hA s p hs hp.le < ⊤)
    (haq : CoarseDeGiorgi.besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le < ⊤) :
    CoarseDeGiorgi.upperMoment a ha s p hs hp.le < ⊤ ∧
      0 < CoarseDeGiorgi.lowerMoment a ha t q ht hq.le ∧
      CoarseDeGiorgi.contrast a ha s t p q hs ht hp.le hq.le ≤
        ENNReal.ofReal ((d.factorial : ℝ) ^ 2) *
          (CoarseDeGiorgi.besovCubeNorm a hA s p hs hp.le *
            CoarseDeGiorgi.besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le) := by
  obtain ⟨h1, h2, h3⟩ := CoarseDeGiorgi.moment_bounds_besov d hd p q s t hp hq hs ht
    a ha hA hAinv hap haq
  refine ⟨?_, ?_, by simpa only [mul_assoc] using h3⟩
  · exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hap)
  · have hne : (CoarseDeGiorgi.lowerMoment a ha t q ht hq.le)⁻¹ ≠ ⊤ :=
      (lt_of_le_of_lt h2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top haq)).ne
    exact pos_iff_ne_zero.mpr (fun h0 => hne (by simp [h0]))

theorem scale_bound {c N w E : ℝ≥0∞} {C D κ : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hκ : 0 ≤ κ)
    (h : c ≤ ENNReal.ofReal D * N) :
    ENNReal.ofReal C * w * c.rpow κ * E ≤
      ENNReal.ofReal (C * Real.rpow D κ) * w * N.rpow κ * E := by
  have h1 : c.rpow κ ≤ (ENNReal.ofReal D).rpow κ * N.rpow κ := by
    calc c.rpow κ ≤ (ENNReal.ofReal D * N).rpow κ := ENNReal.rpow_le_rpow h hκ
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hκ
  have hDpow : (ENNReal.ofReal D).rpow κ = ENNReal.ofReal (Real.rpow D κ) := by
    change ENNReal.ofReal D ^ κ = ENNReal.ofReal (D ^ κ)
    exact ENNReal.ofReal_rpow_of_nonneg hD hκ
  calc ENNReal.ofReal C * w * c.rpow κ * E
      ≤ ENNReal.ofReal C * w * ((ENNReal.ofReal D).rpow κ * N.rpow κ) * E := by gcongr
    _ = (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow D κ)) * w * N.rpow κ * E := by
        rw [hDpow]; ac_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul hC]

end CoarseDeGiorgiAudit.Solution.BridgeBesovCube
