import CoarseDeGiorgi.Foundations.Reconstruction.AssemblySeminorm
import CoarseDeGiorgi.Foundations.Reconstruction.KernelBlocks
import CoarseDeGiorgi.Foundations.Reconstruction.Representatives

/-! # The concrete smooth telescope and its translation to the auxiliary cube -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section
variable {d : ℕ}

/-- The actual unnormalized mean over the reflected integration box. -/
def assemblyMean (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) : ℝ :=
  ((2 * auxSide m) ^ d)⁻¹ * ∫ y in reflectionBox m, reflectedScalar m z w y ∂volume

/-- Step 5's lowest block and subsequent differences of smooth averages. -/
def assemblyBlock (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) : ℕ → Vec d → ℝ
  | 0 => fun x => smoothAverage m (auxSide m) z w x - assemblyMean m z w
  | n + 1 => fun x => smoothAverage m (auxSide (m + (n + 1 : ℕ))) z w x -
      smoothAverage m (auxSide (m + n)) z w x

theorem assembly_smoothAverage_measurable (m : ℤ) (t : ℝ) (ht : 0 < t)
    (htsmall : t ≤ auxSide m) (z : Fin d → ℤ) {w : Vec d → ℝ}
    (hw : Measurable w) : Measurable (smoothAverage m t z w) := by
  have hfold : Measurable (reflectedScalar m z w) := by
    apply hw.comp
    exact measurable_const.add (measurable_pi_iff.mpr fun i => (continuous_apply i).abs.measurable)
  exact ((hfold.comp measurable_snd).mul
    ((contDiff_periodicRho ht htsmall).continuous.measurable.comp
      (measurable_fst.sub measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

theorem assembly_side_le (m : ℤ) (n : ℕ) : auxSide (m + n) ≤ auxSide m := by
  unfold auxSide
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)

theorem assembly_block_measurable (m : ℤ) (z : Fin d → ℤ) {w : Vec d → ℝ}
    (hw : Measurable w) (n : ℕ) : Measurable (assemblyBlock m z w n) := by
  cases n with
  | zero => exact (assembly_smoothAverage_measurable m _ (auxSide_pos m) le_rfl z hw).sub_const _
  | succ n =>
    exact (assembly_smoothAverage_measurable m _ (auxSide_pos _) (assembly_side_le m _) z hw).sub
      (assembly_smoothAverage_measurable m _ (auxSide_pos _) (assembly_side_le m _) z hw)

theorem assembly_block_telescope (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ)
    (n : ℕ) (x : Vec d) :
    (∑ j ∈ Finset.range (n + 1), assemblyBlock m z w j x) =
      smoothAverage m (auxSide (m + n)) z w x - assemblyMean m z w := by
  induction n with
  | zero => simp [assemblyBlock]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [assemblyBlock]; ring

theorem assembly_positiveBox_subset (m : ℤ) :
    reflectionPositiveBox (d := d) m ⊆ reflectionBox m := by
  intro x hx i
  rw [abs_of_pos (hx i).1]
  exact (hx i).2

theorem assembly_reflectionBox_measurable (m : ℤ) : MeasurableSet (reflectionBox (d := d) m) := by
  simp only [reflectionBox, ← Set.iInter_ofPred]
  exact MeasurableSet.iInter fun i =>
    (isOpen_lt (continuous_apply i).abs continuous_const).measurableSet

/-- Translating the positive orthant changes neither distances nor unnormalized volume. -/
theorem assembly_seminorm_translate (m : ℤ) (z : Fin d → ℤ) (α r : ℝ)
    (w : Vec d → ℝ) :
    CoarseDeGiorgi.fracSeminorm (reflectionPositiveBox m) α r
      (fun x => w (auxLower m z + x)) =
    CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w := by
  let T := Homeomorph.addLeft (auxLower m z)
  have hpre : reflectionPositiveBox m = T ⁻¹' auxCube m z :=
    reflectionPositiveBox_eq_preimage_auxCube m z
  have hT : MeasurePreserving T (volume.restrict (reflectionPositiveBox m))
      (volume.restrict (auxCube m z)) := by
    rw [hpre]
    exact (measurePreserving_add_left (volume : Measure (Vec d)) _).restrict_preimage_emb
      T.measurableEmbedding _
  have hp := hT.prod hT
  have hemb := T.measurableEmbedding.prodMap T.measurableEmbedding
  rw [← fracSeminorm_eq_statement, ← fracSeminorm_eq_statement,
    FracGeometry.fracSeminorm_eq_eFracSeminorm, FracGeometry.fracSeminorm_eq_eFracSeminorm]
  unfold Euclid.eFracSeminorm
  congr 1
  have heq := hp.lintegral_comp_emb hemb (Euclid.euclidKernel ((d : ℝ) + α * r) r w)
  change (∫⁻ p, Euclid.euclidKernel ((d : ℝ) + α * r) r
    (fun x => w (auxLower m z + x)) p
      ∂((volume.restrict (reflectionPositiveBox m)).prod (volume.restrict (reflectionPositiveBox m)))) = _
  refine Eq.trans ?_ heq
  apply lintegral_congr
  intro p
  change ENNReal.ofReal (|w (auxLower m z + p.1) - w (auxLower m z + p.2)| ^ r /
    Euclid.eNorm2 (p.1 - p.2) ^ ((d : ℝ) + α * r)) =
    ENNReal.ofReal (|w (auxLower m z + p.1) - w (auxLower m z + p.2)| ^ r /
    Euclid.eNorm2 ((auxLower m z + p.1) - (auxLower m z + p.2)) ^ ((d : ℝ) + α * r))
  rw [add_sub_add_left_eq_sub]

/-- On the positive orthant the actual even reflection is the translated original. -/
theorem assembly_reflected_seminorm (m : ℤ) (z : Fin d → ℤ) (α r : ℝ)
    (w : Vec d → ℝ) :
    CoarseDeGiorgi.fracSeminorm (reflectionPositiveBox m) α r (reflectedScalar m z w) =
      CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w := by
  rw [← assembly_seminorm_translate m z α r w, ← fracSeminorm_eq_statement,
    ← fracSeminorm_eq_statement]
  apply fracSeminorm_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_reflectionPositiveBox m).measurableSet] with x hx
  unfold reflectedScalar
  congr 2
  ext i
  exact abs_of_pos (hx i).1

/-- The additive mean cancels in the exact fractional seminorm. -/
theorem assembly_seminorm_sub_const (V : Set (Vec d)) (α r c : ℝ) (w : Vec d → ℝ) :
    CoarseDeGiorgi.fracSeminorm V α r (fun x => w x - c) =
      CoarseDeGiorgi.fracSeminorm V α r w := by
  simpa only [sub_eq_add_neg, fracSeminorm_eq_statement] using fracSeminorm_add_const V α r (-c) w

end
end CoarseDeGiorgi.Foundations.Reconstruction
