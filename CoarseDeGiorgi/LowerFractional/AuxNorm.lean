module

public import CoarseDeGiorgi.LowerFractional.DescendantHolder
public import CoarseDeGiorgi.LowerFractional.AuxPower
public import CoarseDeGiorgi.LowerFractional.CubeScale

/-! The actual Lr spatial estimate for the auxiliary averages. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

lemma lower_cellAverage_nonneg {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (q : ℝ) :
    0 ≤ lowerCellAverage a ha k q := by
  rw [← lower_spatial_weight_eq_cellAverage]
  exact Finset.sum_nonneg fun η _ => mul_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem lower_auxAverage_norm {d : ℕ} [NeZero d] (m k : ℤ) (hmk : m ≤ k)
    (z : Fin d → ℤ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (hQ : auxCube m z ⊆ Aliases.originCube 1)
    (haQ : IsWeightedCoeffOn (auxCube m z) a)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : MemH1a a (auxCube m z) w G)
    {q : ℝ} (hq : 1 < q) :
    eLpNorm (fun x => euclidNorm (auxAverage m k z G x)) (ENNReal.ofReal (paramR q))
      (volume.restrict (auxCube m z)) ≤
        (ENNReal.ofReal (lowerCellAverage a ha k.toNat q)) ^ (1 / (2 * q)) *
          (weightedEnergy a (auxCube m z) G) ^ (1 / 2 : ℝ) := by
  have hr : 0 < paramR q := zero_lt_one.trans (lower_paramR_gt_one hq)
  have hk : 0 ≤ k := (lower_aux_scale_nonneg m z hQ).trans hmk
  have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  have hb := lower_descendant_spatial_holder m k.toNat (by simpa only [hkn] using hmk)
    z a ha hQ haQ hw hq
  rw [hkn] at hb
  have hL := lower_cellAverage_nonneg k.toNat a ha q
  have hE := (Weighted.MemH1a.energy_lt_top (auxCube_isOpenBoundedConvexDomain m z).isOpen haQ hw).ne
  have hi : (∫⁻ x in auxCube m z,
      (ENNReal.ofReal (euclidNorm (auxAverage m k z G x))) ^ paramR q) ≤
        (ENNReal.ofReal (lowerCellAverage a ha k.toNat q)) ^ (paramR q / (2 * q)) *
          (weightedEnergy a (auxCube m z) G) ^ (paramR q / 2) := by
    rw [lower_auxAverage_power_integral m k hmk z G hr]
    have hh := ENNReal.ofReal_le_ofReal hb
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hL _),
      ← ENNReal.ofReal_rpow_of_nonneg hL (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hE] at hh
    exact hh
  have hm : AEStronglyMeasurable (fun x => euclidNorm (auxAverage m k z G x))
      (volume.restrict (auxCube m z)) :=
    (Foundations.Reconstruction.measurable_euclidNorm_auxAverage m k z G).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal hr.le]
  have he : (fun x => ‖euclidNorm (auxAverage m k z G x)‖ₑ ^ paramR q) =
      fun x => ENNReal.ofReal (euclidNorm (auxAverage m k z G x)) ^ paramR q := by
    funext x
    rw [← ofReal_norm, Real.norm_of_nonneg
      (show 0 ≤ euclidNorm (auxAverage m k z G x) from Real.sqrt_nonneg _)]
  rw [he]
  have hh := ENNReal.rpow_le_rpow hi (div_nonneg zero_le_one hr.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hh
  have hexp : (paramR q / (2 * q)) * (1 / paramR q) = 1 / (2 * q) := by field_simp
  have hexp' : (paramR q / 2) * (1 / paramR q) = (1 / 2 : ℝ) := by field_simp
  rw [hexp, hexp'] at hh
  exact hh


end CoarseDeGiorgi.LowerFractional
