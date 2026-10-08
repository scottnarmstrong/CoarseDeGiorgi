import CoarseDeGiorgi.Foundations.Reconstruction.AuxFaceClosure

/-! # Measure-preserving coordinate sign changes for the reflected box -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- A coordinate sign choice is an involution. -/
theorem signLinear_involutive (s : Fin d → Bool) : Function.Involutive (signLinear s) := by
  intro x
  ext i
  simp only [signLinear_apply, ← mul_assoc, reflectionSign_sq, one_mul]

/-- Coordinate sign changes are continuous self-inverse transformations of the carrier. -/
def signHomeomorph (s : Fin d → Bool) : Vec d ≃ₜ Vec d where
  toFun := signLinear s
  invFun := signLinear s
  left_inv := signLinear_involutive s
  right_inv := signLinear_involutive s
  continuous_toFun := (signLinear s).continuous
  continuous_invFun := (signLinear s).continuous

/-- Reflection preserves unnormalized Lebesgue measure in any dimension. -/
theorem measurePreserving_signLinear (s : Fin d → Bool) : MeasurePreserving (signLinear s) := by
  have hcoord (i : Fin d) : MeasurePreserving (fun t : ℝ => reflectionSign (s i) * t) := by
    cases hs : s i
    · simpa only [hs, reflectionSign, Bool.false_eq_true, ite_false, neg_one_mul] using
        (Measure.measurePreserving_neg (volume : Measure ℝ))
    · simp only [reflectionSign, ite_true, one_mul]
      exact ⟨measurable_id, Measure.map_id⟩
  exact volume_preserving_pi hcoord

/-- The positive cell from which the full reflected box is constructed. -/
def reflectionPositiveBox (m : ℤ) : Set (Vec d) :=
  {x | ∀ i, 0 < x i ∧ x i < auxSide m}

/-- One open orthant of the reflected box. -/
def reflectionOrthant (m : ℤ) (s : Fin d → Bool) : Set (Vec d) :=
  (signLinear s) ⁻¹' reflectionPositiveBox m

theorem measurePreserving_signLinear_restrict (m : ℤ) (s : Fin d → Bool) :
    MeasurePreserving (signLinear s)
      (volume.restrict (reflectionOrthant m s))
      (volume.restrict (reflectionPositiveBox m)) :=
  (measurePreserving_signLinear s).restrict_preimage_emb
    (signHomeomorph s).measurableEmbedding (reflectionPositiveBox m)

theorem setIntegral_signLinear_orthant (m : ℤ) (s : Fin d → Bool)
    (f : Vec d → ℝ) :
    ∫ x in reflectionOrthant m s, f (signLinear s x) ∂volume =
      ∫ x in reflectionPositiveBox m, f x ∂volume :=
  (measurePreserving_signLinear_restrict m s).integral_comp
    (signHomeomorph s).measurableEmbedding f

/-- In the positive cell, absolute-value folding undoes every sign choice. -/
theorem abs_signLinear_of_mem_positive (m : ℤ) (s : Fin d → Bool) {x : Vec d}
    (hx : x ∈ reflectionPositiveBox m) :
    (fun i => |signLinear s x i|) = x := by
  ext i
  rw [signLinear_apply, abs_mul, abs_of_pos (hx i).1]
  cases hs : s i <;> norm_num [reflectionSign, hs]

/-- The positive cell is exactly the pullback of the auxiliary cube. -/
theorem reflectionPositiveBox_eq_preimage_auxCube (m : ℤ) (z : Fin d → ℤ) :
    reflectionPositiveBox m = (fun x => auxLower m z + x) ⁻¹' auxCube m z := by
  ext x
  exact (auxLower_add_mem_auxCube m z x).symm

/-- Open orthants associated with different sign choices are disjoint. -/
theorem pairwise_disjoint_reflectionOrthant (m : ℤ) :
    Pairwise (fun s t : Fin d → Bool => Disjoint (reflectionOrthant m s) (reflectionOrthant m t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hs
  have hex : ∃ i, s i ≠ t i := Function.ne_iff.mp hst
  obtain ⟨i, hi⟩ := hex
  have hxs : 0 < reflectionSign (s i) * x i := (hx i).1
  have hxt : 0 < reflectionSign (t i) * x i := (hs i).1
  cases hsi : s i <;> cases hti : t i
  · exact hi (hsi.trans hti.symm)
  · simp only [hsi, hti, reflectionSign, Bool.false_eq_true, ite_false, ite_true,
      neg_one_mul, one_mul] at hxs hxt
    linarith only [hxs, hxt]
  · simp only [hsi, hti, reflectionSign, Bool.false_eq_true, ite_false, ite_true,
      neg_one_mul, one_mul] at hxs hxt
    linarith only [hxs, hxt]
  · exact hi (hsi.trans hti.symm)

end

end CoarseDeGiorgi.Foundations.Reconstruction
