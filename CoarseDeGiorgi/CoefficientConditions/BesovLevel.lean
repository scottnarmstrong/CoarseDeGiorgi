import CoarseDeGiorgi.CoefficientConditions.BesovMatrix
import CoarseDeGiorgi.CoefficientConditions.BesovGeom
import CoarseDeGiorgi.Besov.CellBounds

/-! # One level: the mean over simplices against the mean over cubes -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.CoefficientConditions

/-- The mean over the cubes of level `k`, as in `besovCubeNorm`. -/
noncomputable def cubeMean {d : ℕ} (b : Vec d → Mat d) (k : ℕ) (p : ℝ) : ℝ :=
  (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeSet k j) b‖ p) /
    ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)

theorem simplexSum_le {d : ℕ} (b : Vec d → Mat d) (hb : IsWeightedCoeffOn (originCube 1) b)
    (k : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) /
      ((triangulation (d := d) k).card : ℝ) ≤
    Real.rpow (d.factorial : ℝ) p * cubeMean b k p := by
  classical
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hinj : Function.Injective
      (fun jp : (Fin d → Fin (3 ^ k)) × Equiv.Perm (Fin d) =>
        (gridOffset k jp.1, jp.2)) := by
    intro jp lp h
    have h' : (gridOffset k jp.1, jp.2) = (gridOffset k lp.1, lp.2) := h
    have h1 : jp.1 = lp.1 := Moments.gridOffset_injective k (Prod.mk.inj h').1
    have h2 : jp.2 = lp.2 := (Prod.mk.inj h').2
    exact Prod.ext_iff.2 ⟨h1, h2⟩
  let F : (Fin d → ℤ) × Equiv.Perm (Fin d) → ℝ := fun v =>
    Real.rpow ‖volumeAverageMat (CoarseDeGiorgi.simplex (-(k : ℤ)) v.2
      (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (v.1 i : ℝ))) b‖ p
  have hsum : ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) =
      ∑ j : Fin d → Fin (3 ^ k), ∑ π : Equiv.Perm (Fin d), F (gridOffset k j, π) := by
    have h1 := Finset.sum_attach (triangulation (d := d) k) F
    refine Eq.trans h1 ?_
    unfold CoarseDeGiorgi.triangulation
    rw [Finset.sum_image (fun x _ y _ h => hinj h), Fintype.sum_prod_type]
  have hcard : ((triangulation (d := d) k).card : ℝ) =
      (d.factorial : ℝ) * ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ) := by
    have := Moments.triangulation_card (d := d) k
    have h2 : ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card) = 3 ^ (k * d) := by
      simp [Finset.card_univ, ← pow_mul, Nat.mul_comm]
    rw [h2]
    exact_mod_cast this
  have hF (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) :
      F (gridOffset k j, π) ≤
        Real.rpow (d.factorial : ℝ) p * Real.rpow ‖volumeAverageMat (cubeSet k j) b‖ p := by
    have hn : ‖volumeAverageMat (cellSet k j π) b‖ ≤
        (d.factorial : ℝ) * ‖volumeAverageMat (cubeSet k j) b‖ :=
      norm_average_le (isWeightedCoeffOn_mono (cubeSet_subset_originCube k j) hb)
        (cellSet_subset k j π) (volume_cubeSet_eq k j π) (volume_cellSet_ne_zero k j π)
        (volume_cellSet_ne_top k j π)
    change Real.rpow ‖volumeAverageMat (cellSet k j π) b‖ p ≤ _
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow,
      ← Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hn hp0
  have hfpos : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hcpos : (0 : ℝ) < ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ) := by
    have : 0 < (Finset.univ : Finset (Fin d → Fin (3 ^ k))).card := by
      apply Finset.card_pos.2; exact Finset.univ_nonempty
    exact_mod_cast this
  rw [hsum, hcard, cubeMean]
  have hle : ∑ j : Fin d → Fin (3 ^ k), ∑ π : Equiv.Perm (Fin d), F (gridOffset k j, π) ≤
      (d.factorial : ℝ) * (Real.rpow (d.factorial : ℝ) p *
        ∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeSet k j) b‖ p) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    calc ∑ π : Equiv.Perm (Fin d), F (gridOffset k j, π)
        ≤ ∑ _π : Equiv.Perm (Fin d), Real.rpow (d.factorial : ℝ) p *
            Real.rpow ‖volumeAverageMat (cubeSet k j) b‖ p :=
          Finset.sum_le_sum (fun π _ => hF j π)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := hle
    _ = _ := by field_simp

end CoarseDeGiorgi.CoefficientConditions
