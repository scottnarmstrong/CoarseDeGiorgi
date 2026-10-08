module

public import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationMembership
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The interface cylinder has ambient volume zero. A coordinate slice fixes
all but one transverse coordinate, and each such fiber contains at most two
points. -/
theorem polynomialInterface_volume_zero {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {epsilon : ℝ} (_he : 0 < epsilon) :
    volume {x : Vec d | Sharpness.transverseNorm x = 2 * epsilon} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  let j : Fin (n + 1) := ⟨1, by omega⟩
  let e₀ : MeasurableEquiv (Vec (n + 1))
      (ℝ × (Fin n → ℝ)) := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) j
  let e : MeasurableEquiv (Vec (n + 1)) ((Fin n → ℝ) × ℝ) :=
    e₀.trans MeasurableEquiv.prodComm
  let T : Set ((Fin n → ℝ) × ℝ) :=
    {p | Sharpness.transverseNorm (e.symm p) = 2 * epsilon}
  have hmp : MeasurePreserving e volume (volume.prod volume) := by
    exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).trans
      Measure.measurePreserving_swap
  have hTmeas : MeasurableSet T := by
    have hclosed : IsClosed {x : Vec (n + 1) |
        Sharpness.transverseNorm x = 2 * epsilon} :=
      isClosed_eq Sharpness.lineRadius_continuous continuous_const
    exact hclosed.measurableSet.preimage e.symm.measurable
  have hfiber : ∀ z : Fin n → ℝ, volume {t : ℝ | (z, t) ∈ T} = 0 := by
    intro z
    let x : ℝ → Vec (n + 1) := fun t => e.symm (z, t)
    have hx (t : ℝ) : x t = j.insertNth t z := by
      simp [x, e, e₀, MeasurableEquiv.prodComm]
      rfl
    have hcoordj (t : ℝ) : x t j = t := by
      rw [hx t]
      simp
    have hcoord_other (t t₀ : ℝ) (i : Fin (n + 1)) (hi : i ≠ j) :
        x t i = x t₀ i := by
      rw [hx t, hx t₀]
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hi
      rw [← hk]
      simp
    have hfinite : {t : ℝ | (z, t) ∈ T}.Finite := by
      by_cases hne : ({t : ℝ | (z, t) ∈ T}).Nonempty
      · obtain ⟨t₀, ht₀⟩ := hne
        have hfiniteInsert : (insert t₀ ({-t₀} : Set ℝ)).Finite :=
          Set.finite_insert.mpr (Set.finite_singleton (-t₀))
        apply hfiniteInsert.subset
        intro t ht
        have hrad (t' : ℝ) (h : (z, t') ∈ T) :
            vecNormSq (Sharpness.transversePart (x t')) = (2 * epsilon) ^ 2 := by
          have hs := congrArg (fun a : ℝ => a ^ 2) h
          simpa [T, Sharpness.transverseNorm, Homogenization.euclideanNorm_sq] using hs
        have hdiff :
            vecNormSq (Sharpness.transversePart (x t)) -
              vecNormSq (Sharpness.transversePart (x t₀)) = t ^ 2 - t₀ ^ 2 := by
          unfold vecNormSq vecDot
          rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
          · have hjt : Sharpness.transversePart (x t) j = t := by
              simp [Sharpness.transversePart, j, hcoordj]
            have hjt₀ : Sharpness.transversePart (x t₀) j = t₀ := by
              simp [Sharpness.transversePart, j, hcoordj]
            rw [hjt, hjt₀]
            nlinarith
          · intro i hi hij
            simp [Sharpness.transversePart, hcoord_other t t₀ i hij]
          · simp
        have hsquares : t ^ 2 = t₀ ^ 2 := by
          have h1 := hrad t ht
          have h0 := hrad t₀ ht₀
          rw [h1, h0] at hdiff
          linarith
        have hfac : (t - t₀) * (t + t₀) = 0 := by nlinarith
        rcases mul_eq_zero.mp hfac with h | h
        · exact Set.mem_insert_iff.mpr (Or.inl (sub_eq_zero.mp h))
        · apply Set.mem_insert_iff.mpr
          right
          simp
          linarith
      · have hempty : {t : ℝ | (z, t) ∈ T} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hne ⟨t, ht⟩
        rw [hempty]
        exact Set.finite_empty
    exact hfinite.measure_zero volume
  have hTzero : volume.prod volume T = 0 := by
    apply Measure.measure_prod_null_of_ae_null hTmeas
    filter_upwards [] with z
    change volume {t : ℝ | (z, t) ∈ T} = 0
    exact hfiber z
  have hprezero : volume (e ⁻¹' T) = 0 := by
    calc
      volume (e ⁻¹' T) = Measure.map e volume T := by
        rw [Measure.map_apply e.measurable hTmeas]
      _ = volume.prod volume T := by rw [hmp.map_eq]
      _ = 0 := hTzero
  have hset : {x : Vec (n + 1) | Sharpness.transverseNorm x = 2 * epsilon} =
      e ⁻¹' T := by
    ext x
    simp [T]
  rw [hset]
  exact hprezero

end

end CoarseDeGiorgi.SharpnessExamples
