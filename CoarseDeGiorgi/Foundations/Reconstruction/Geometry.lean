module

public import CoarseDeGiorgi.Foundations.Reconstruction.Defs

/-! # Geometry of the exact auxiliary cube and its descendants -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The side length of the auxiliary root. -/
def auxSide (m : ℤ) : ℝ := (3 : ℝ) ^ (1 - m)

/-- The lower corner used in the even-reflection construction. -/
def auxLower (m : ℤ) (z : Fin d → ℤ) : Vec d :=
  fun i => (z i : ℝ) * (3 : ℝ) ^ (-m) - auxSide m / 2

theorem auxSide_pos (m : ℤ) : 0 < auxSide m :=
  zpow_pos (by norm_num) _

theorem auxCube_eq_pi_Ioo (m : ℤ) (z : Fin d → ℤ) :
    auxCube m z = Set.pi Set.univ (fun i =>
      Set.Ioo (auxLower m z i) (auxLower m z i + auxSide m)) := by
  ext x
  simp only [auxCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_Ioo, auxLower, auxSide, abs_lt]
  constructor <;> intro h i <;> specialize h i <;> constructor <;> linarith only [h.1, h.2]

theorem isOpen_auxCube (m : ℤ) (z : Fin d → ℤ) : IsOpen (auxCube m z) := by
  change IsOpen {x : Vec d | ∀ i, |x i - (z i : ℝ) * (3 : ℝ) ^ (-m)| <
      ((3 : ℝ) ^ (1 - m)) / 2}
  simp only [← Set.iInter_ofPred]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).sub continuous_const).abs continuous_const

theorem measurableSet_auxCube (m : ℤ) (z : Fin d → ℤ) :
    MeasurableSet (auxCube m z) := (isOpen_auxCube m z).measurableSet

theorem volume_auxCube (m : ℤ) (z : Fin d → ℤ) :
    volume (auxCube m z) = ENNReal.ofReal ((auxSide m) ^ d) := by
  rw [auxCube_eq_pi_Ioo, Real.volume_pi_Ioo]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (auxSide_pos m).le]

theorem volume_auxCube_ne_zero (m : ℤ) (z : Fin d → ℤ) :
    volume (auxCube m z) ≠ 0 := by
  rw [volume_auxCube]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos (auxSide_pos m) d))

theorem volume_auxCube_ne_top (m : ℤ) (z : Fin d → ℤ) :
    volume (auxCube m z) ≠ ⊤ := by
  rw [volume_auxCube]
  exact ENNReal.ofReal_ne_top

/-- Descendants have the exact copied normalization, independently of the offset. -/
theorem volume_auxDescendantCube (m k : ℤ) (z n : Fin d → ℤ) :
    volume (auxDescendantCube m k z n) = ENNReal.ofReal ((auxSide k) ^ d) := by
  have heq : auxDescendantCube m k z n = Set.pi Set.univ (fun i => Set.Ioo
      ((z i : ℝ) * (3 : ℝ) ^ (-m) + (n i : ℝ) * auxSide k - auxSide k / 2)
      ((z i : ℝ) * (3 : ℝ) ^ (-m) + (n i : ℝ) * auxSide k + auxSide k / 2)) := by
    ext x
    simp only [auxDescendantCube, auxSide, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_Ioo, abs_lt]
    constructor <;> intro h i <;> specialize h i <;> constructor <;>
      linarith only [h.1, h.2]
  rw [heq, Real.volume_pi_Ioo]
  simp only [show ∀ c : ℝ, c + auxSide k / 2 - (c - auxSide k / 2) = auxSide k
    from fun c => by ring, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (auxSide_pos k).le]

theorem isOpen_auxDescendantCube (m k : ℤ) (z n : Fin d → ℤ) :
    IsOpen (auxDescendantCube m k z n) := by
  change IsOpen {x : Vec d | ∀ i, |x i - ((z i : ℝ) * (3 : ℝ) ^ (-m) +
      (n i : ℝ) * (3 : ℝ) ^ (1 - k))| < ((3 : ℝ) ^ (1 - k)) / 2}
  simp only [← Set.iInter_ofPred]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).sub continuous_const).abs continuous_const

theorem measurableSet_auxDescendantCube (m k : ℤ) (z n : Fin d → ℤ) :
    MeasurableSet (auxDescendantCube m k z n) :=
  (isOpen_auxDescendantCube m k z n).measurableSet

/-- Every fixed-scale average is measurable even for an arbitrary input field. -/
theorem measurable_auxAverage (m k : ℤ) (z : Fin d → ℤ) (f : Vec d → Vec d) :
    Measurable (auxAverage m k z f) := by
  classical
  unfold auxAverage
  apply Finset.measurable_sum
  intro n _
  exact Measurable.ite (measurableSet_auxDescendantCube m k z n)
    measurable_const measurable_const

/-- The Euclidean length of the step field is measurable in the carrier's Borel structure. -/
theorem measurable_euclidNorm_auxAverage (m k : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) : Measurable (fun x => euclidNorm (auxAverage m k z f x)) :=
  Euclid.continuous_eNorm2.measurable.comp (measurable_auxAverage m k z f)

/-- Reflection maps the positive orthant cube to the exact auxiliary root. -/
theorem auxLower_add_mem_auxCube (m : ℤ) (z : Fin d → ℤ) (x : Vec d) :
    auxLower m z + x ∈ auxCube m z ↔ ∀ i, 0 < x i ∧ x i < auxSide m := by
  rw [auxCube_eq_pi_Ioo]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo, Pi.add_apply,
    lt_add_iff_pos_right, add_lt_add_iff_left]

end

end CoarseDeGiorgi.Foundations.Reconstruction
