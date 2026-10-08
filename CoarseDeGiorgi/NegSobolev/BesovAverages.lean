import Homogenization.Ambient.CoefficientField
import Homogenization.CoarseGraining.Definitions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.CubeCell
import CoarseDeGiorgi.Statements.SimplexCell
import CoarseDeGiorgi.Statements.Triangulation
import CoarseDeGiorgi.Statements.GaussianKernel

import CoarseDeGiorgi.Statements.IsOpenOriginCube
import CoarseDeGiorgi.NegSobolev.BesovGeometry
import CoarseDeGiorgi.NegSobolev.BesovLevel
import CoarseDeGiorgi.NegSobolev.BesovSeries

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- `p.besov.averages`, finite `1 ≤ p < ∞`: there is
`C = C(d) > 0` such that for every `1 ≤ p < ∞`, every matrix field `b` on `□₀`, symmetric and
positive semidefinite a.e. with `|b| ∈ L¹(□₀)`, and every `k ≥ 0`, for both families `𝒫_k`
(the simplices of `𝒯_k`, and the cubes `z + □_{-k}`, `z ∈ 3^{-k}ℤ^d ∩ □₀`),
`C⁻¹ (avsum_{Q ∈ 𝒫_k} |(b)_Q|^p)^{1/p} ≤ ‖G_{3^{-2k}} * b̃‖_{L^p(ℝ^d)} ≤ C (avsum …)^{1/p}`
(`e.besov.heat`), and consequently, for every `s > 0`, each of the sums
`∑_k 3^{-ks} (avsum_{Q ∈ 𝒫_k} |(b)_Q|^p)^{1/(2p)}` and `∑_k 3^{-ks} ‖G_{3^{-2k}} * b̃‖_{L^p}^{1/2}`
is at most `C^{1/2}` times the other (`e.besov.averages`). Here `b̃` is the extension of `b` by
zero (`(originCube 1).indicator b`), `G_t * b̃` is the entrywise convolution
`x ↦ ∫ G_t(x - y) b̃(y) dy`, `|·|` is the operator norm (the `L^p` norm of a matrix field is that
of its operator norm), and the means are the arithmetic means over the `3^{kd} d!`
simplices (normalized as in `upperCellAverage`) and over the `3^{kd}` cubes (as in
`besovCubeNorm`, whose cube sum squared is the first sum for the cubes). The case `p = ∞`
(maxima) is not formalized. -/
theorem besov_averages_proved (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℝ), 1 ≤ p →
      ∀ (b : Vec d → Mat d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), (b x).PosSemidef) →
        (∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1))) →
        let heat : ℕ → ℝ≥0∞ := fun k =>
          eLpNorm
            (fun x => ‖Matrix.of fun i j =>
              ∫ y, gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) *
                (originCube 1).indicator b y i j ∂volume‖)
            (ENNReal.ofReal p) volume
        let simplexMean : ℕ → ℝ := fun k =>
          ((triangulation (d := d) k).attach.sum fun η =>
              Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) /
            ((triangulation (d := d) k).card : ℝ)
        let cubeMean : ℕ → ℝ := fun k =>
          (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeCell k j) b‖ p) /
            ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)
        (∀ k : ℕ,
          ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (simplexMean k)).rpow (1 / p) ≤ heat k ∧
            heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (simplexMean k)).rpow (1 / p)) ∧
        (∀ k : ℕ,
          ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (cubeMean k)).rpow (1 / p) ≤ heat k ∧
            heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (cubeMean k)).rpow (1 / p)) ∧
        ∀ s : ℝ, 0 < s →
          let heatSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (heat k).rpow (1 / 2)
          let simplexSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
              (ENNReal.ofReal (simplexMean k)).rpow (1 / (2 * p))
          let cubeSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
              (ENNReal.ofReal (cubeMean k)).rpow (1 / (2 * p))
          (simplexSum ≤ ENNReal.ofReal (Real.sqrt C) * heatSum ∧
            heatSum ≤ ENNReal.ofReal (Real.sqrt C) * simplexSum) ∧
          (cubeSum ≤ ENNReal.ofReal (Real.sqrt C) * heatSum ∧
            heatSum ≤ ENNReal.ofReal (Real.sqrt C) * cubeSum) := by
  classical
  let c : ℝ := (4 * Real.pi) ^ (-((d : ℝ) / 2)) * Real.exp (-((d : ℝ) / 4))
  let δ : ℝ := c / (d.factorial : ℝ)
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)
  let C : ℝ := max δ⁻¹ D
  have hc : 0 < c := by dsimp [c]; positivity
  have hf : (0 : ℝ) < d.factorial := Nat.cast_pos.mpr (Nat.factorial_pos d)
  have hδ : 0 < δ := div_pos hc hf
  have hCδ : δ⁻¹ ≤ C := le_max_left _ _
  have hCD : D ≤ C := le_max_right _ _
  have hC : 0 < C := (inv_pos.mpr hδ).trans_le hCδ
  have hδc : δ ≤ c := by
    apply (div_le_iff₀ hf).mpr
    have hf1 : (1 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos d)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf1 hc.le
  refine ⟨C, hC, ?_⟩
  intro p hp b hpos hb
  have hV : MeasurableSet (originCube (d := d) 1) := (isOpen_originCube 1).measurableSet
  let heat : ℕ → ℝ≥0∞ := fun k =>
    eLpNorm
      (fun x => ‖Matrix.of fun i j =>
        ∫ y, gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) *
          (originCube 1).indicator b y i j ∂volume‖)
      (ENNReal.ofReal p) volume
  let simplexMean : ℕ → ℝ := fun k =>
    ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) /
      ((triangulation (d := d) k).card : ℝ)
  let cubeMean : ℕ → ℝ := fun k =>
    (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeCell k j) b‖ p) /
      ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)
  have hnormS (k : ℕ) (η : SimplexIndex d k) :
      ((4 * Real.pi * (3 : ℝ) ^ (-(2 * (k : ℤ)))) ^ (-((d : ℝ) / 2)) *
        Real.exp (-((d : ℝ) / 4))) * (volume (simplexCell k η)).toReal = δ := by
    rw [triadic_time_eq_side_sq, simplexCell_volume_side]
    calc
      _ = ((4 * Real.pi * ((3 : ℝ) ^ (-(k : ℤ))) ^ 2) ^ (-((d : ℝ) / 2)) *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ d) * Real.exp (-((d : ℝ) / 4)) / (d.factorial : ℝ) := by ring
      _ = δ := by rw [gaussianKernel_prefactor_mul_side_volume d _ (zpow_pos (by norm_num) _)]
  have hnormQ (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
      ((4 * Real.pi * (3 : ℝ) ^ (-(2 * (k : ℤ)))) ^ (-((d : ℝ) / 2)) *
        Real.exp (-((d : ℝ) / 4))) * (volume (cubeCell k j)).toReal = c := by
    rw [triadic_time_eq_side_sq, cubeCell_volume_side]
    calc
      _ = ((4 * Real.pi * ((3 : ℝ) ^ (-(k : ℤ))) ^ 2) ^ (-((d : ℝ) / 2)) *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ d) * Real.exp (-((d : ℝ) / 4)) := by ring
      _ = c := by rw [gaussianKernel_prefactor_mul_side_volume d _ (zpow_pos (by norm_num) _)]
  have hsimp (k : ℕ) :
      ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (simplexMean k)).rpow (1 / p) ≤ heat k ∧
        heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (simplexMean k)).rpow (1 / p) := by
    have hN : (0 : ℝ) < (triangulation (d := d) k).card :=
      Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)
    have h := besov_level_comparison ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _)
      (originCube 1) hV (simplexCell k)
      (fun η => (simplexCell_isOpenBoundedConvexDomain k η).isOpen.measurableSet)
      (simplexCell_subset_originCube k)
      (Assembly.ClassicalMomentsImpl.simplexCell_pairwise_disjoint k) (simplexCell_measure_partition k)
      ((triangulation (d := d) k).card : ℝ) hN (Assembly.ClassicalMomentsImpl.simplexCell_volume_real k)
      (fun η => (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne)
      (fun η _x hx _y hy => simplexCell_sq_diameter k η hx hy)
      δ hδ (fun η => (hnormS k η).ge) C hC hCδ hCD p hp b hb hpos
    simp_rw [← gaussianKernel_indicator_entry_eq _ _ _ hV b] at h
    dsimp only [simplexMean, heat]
    have hsum : (∑ η : SimplexIndex d k, Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) =
        (triangulation (d := d) k).attach.sum (fun η => Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) := by
      unfold SimplexIndex
      exact Finset.sum_coe_sort_eq_attach _ _
    rw [hsum] at h
    exact h
  have hcube (k : ℕ) :
      ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (cubeMean k)).rpow (1 / p) ≤ heat k ∧
        heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (cubeMean k)).rpow (1 / p) := by
    have hN : (0 : ℝ) < ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ) := by
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      positivity
    have h := besov_level_comparison ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _)
      (originCube 1) hV (cubeCell k)
      (fun j => (cubeCell_isOpenBoundedConvexDomain k j).isOpen.measurableSet)
      (CoefficientConditions.cubeSet_subset_originCube k) (cubeCell_pairwise_disjoint k)
      (cubeCell_measure_partition k) ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)
      hN (cubeCell_volume_real k)
      (fun j => (cubeCell_isOpenBoundedConvexDomain k j).isBoundedDomain.isBounded.measure_lt_top.ne)
      (fun j _x hx _y hy => cubeCell_sq_diameter k j hx hy)
      δ hδ (fun j => by rw [hnormQ k j]; exact hδc) C hC hCδ hCD p hp b hb hpos
    simp_rw [← gaussianKernel_indicator_entry_eq _ _ _ hV b] at h
    exact h
  refine ⟨hsimp, hcube, ?_⟩
  intro s _hs
  exact ⟨besov_series_comparison_of_levels C hC p (fun k => ENNReal.ofReal (simplexMean k))
      heat (fun k => ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))))
      (fun k => (hsimp k).1) (fun k => (hsimp k).2),
    besov_series_comparison_of_levels C hC p (fun k => ENNReal.ofReal (cubeMean k))
      heat (fun k => ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))))
      (fun k => (hcube k).1) (fun k => (hcube k).2)⟩

end CoarseDeGiorgi.NegSobolev
