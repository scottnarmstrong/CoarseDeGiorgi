import CoarseDeGiorgi.Foundations.Reconstruction.AuxIncrementLp

/-! # Reflected cells and parent-cell cancellation -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The affine chart from one reflected orthant to the centered root grid. -/
def reflectionChart (m : ℤ) (z : Fin d → ℤ) (s : Fin d → Bool) : Vec d ≃ₜ Vec d :=
  (signHomeomorph s).trans (Homeomorph.addRight (auxLower m z - auxCenter m z))

/-- Open reflected cells use exactly the translated original descendant grid. -/
def reflectedCell (m : ℤ) (z : Fin d → ℤ) (s : Fin d → Bool)
    (R : TriadicCube d) : Set (Vec d) :=
  reflectionChart m z s ⁻¹' openCubeSet R

theorem measurePreserving_reflectionChart (m : ℤ) (z : Fin d → ℤ)
    (s : Fin d → Bool) : MeasurePreserving (reflectionChart m z s) :=
  (measurePreserving_add_right (volume : Measure (Vec d)) _).comp
    (measurePreserving_signLinear s)

theorem measurePreserving_reflectionChart_restrict (m : ℤ) (z : Fin d → ℤ)
    (s : Fin d → Bool) (R : TriadicCube d) :
    MeasurePreserving (reflectionChart m z s)
      (volume.restrict (reflectedCell m z s R)) (volume.restrict (openCubeSet R)) :=
  (measurePreserving_reflectionChart m z s).restrict_preimage_emb
    (reflectionChart m z s).measurableEmbedding (openCubeSet R)

theorem reflectedCell_subset_of_mem_descendantsAtDepth (m : ℤ) (z : Fin d → ℤ)
    (s : Fin d → Bool) {R S : TriadicCube d} {j : ℕ}
    (hS : S ∈ descendantsAtDepth R j) :
    reflectedCell m z s S ⊆ reflectedCell m z s R :=
  Set.preimage_mono (openCubeSet_subset_of_mem_descendantsAtDepth hS)

theorem reflectedCell_root_eq_orthant (m : ℤ) (z : Fin d → ℤ) (s : Fin d → Bool) :
    reflectedCell m z s (originCube d (1 - m)) = reflectionOrthant m s := by
  ext x
  change reflectionChart m z s x ∈ openCubeSet (originCube d (1 - m)) ↔
    signLinear s x ∈ reflectionPositiveBox m
  rw [reflectionPositiveBox_eq_preimage_auxCube m z, Set.mem_preimage,
    auxCube_eq_translate_originCube m z, mem_translateSet_iff_sub_mem]
  rw [show reflectionChart m z s x = auxLower m z + signLinear s x - auxCenter m z by
    change signLinear s x + (auxLower m z - auxCenter m z) = _
    abel]

/-- Distinct reflected cells in a fixed orthant have disjoint interiors. -/
theorem disjoint_reflectedCell_of_mem_descendantsAtDepth (m : ℤ) (z : Fin d → ℤ)
    (s : Fin d → Bool) {Q R S : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (hS : S ∈ descendantsAtDepth Q j) (hne : R ≠ S) :
    Disjoint (reflectedCell m z s R) (reflectedCell m z s S) := by
  apply Set.disjoint_left.mpr
  intro x hxR hxS
  exact Set.disjoint_left.mp (pairwiseDisjoint_descendantsAtDepth Q j hR hS hne)
    (openCubeSet_subset_cubeSet R hxR) (openCubeSet_subset_cubeSet S hxS)

/-- Reflected cells cover their orthant up to the null internal faces. -/
theorem reflectionOrthant_ae_eq_iUnion_reflectedCell (m : ℤ) (z : Fin d → ℤ)
    (s : Fin d → Bool) (j : ℕ) :
    reflectionOrthant m s =ᵐ[volume]
      ⋃ R ∈ descendantsAtDepth (originCube d (1 - m)) j, reflectedCell m z s R := by
  let Q := originCube d (1 - m)
  have ha : ∀ᵐ y : Vec d ∂volume, ∀ R : TriadicCube d,
      y ∈ cubeSet R ↔ y ∈ openCubeSet R :=
    ae_all_iff.mpr fun R => (cubeSet_ae_eq_openCubeSet R).mono fun _ h => Iff.of_eq h
  have hs : openCubeSet Q =ᵐ[volume] ⋃ R ∈ descendantsAtDepth Q j, openCubeSet R := by
    filter_upwards [ha] with y hy
    apply propext
    rw [← hy Q, cubeSet_eq_iUnion_descendantsAtDepth Q j]
    simp only [Set.mem_iUnion]
    exact exists_congr fun R => exists_congr fun _ => hy R
  have ht := (measurePreserving_reflectionChart m z s).quasiMeasurePreserving.preimage_ae_eq hs
  rw [← reflectedCell_root_eq_orthant m z s]
  simpa only [reflectedCell, Set.preimage_iUnion] using ht

/-- On each orthant the gradient reflection has a fixed sign matrix. -/
theorem reflectedGradient_eq_chart (m : ℤ) (z : Fin d → ℤ) (s : Fin d → Bool)
    (f : Vec d → Vec d) {x : Vec d}
    (hx : x ∈ reflectedCell m z s (originCube d (1 - m))) :
    reflectedGradient m z f x =
      signLinear s (f (reflectionChart m z s x + auxCenter m z)) := by
  have hp : signLinear s x ∈ reflectionPositiveBox m := by
    rwa [reflectedCell_root_eq_orthant] at hx
  have heq : auxLower m z + signLinear s x =
      reflectionChart m z s x + auxCenter m z := by
    change _ = signLinear s x + (auxLower m z - auxCenter m z) + auxCenter m z
    abel
  funext i
  change reflectedPartial m z f i x = _
  calc
    _ = reflectedPartial m z f i (signLinear s (signLinear s x)) :=
      congrArg (reflectedPartial m z f i) (signLinear_involutive s x).symm
    _ = reflectionSign (s i) * f (auxLower m z + signLinear s x) i :=
      reflectedPartial_signLinear m z f i s hp
    _ = _ := by rw [heq]; rfl

/-- The reflected average agrees almost everywhere with the charted vector projection. -/
theorem reflectedAverage_eq_projection_on_cell_ae (m : ℤ) (z : Fin d → ℤ)
    (s : Fin d → Bool) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (1 - m)) j)
    (f : Vec d → Vec d) (k : ℕ) :
    reflectedAverage m k z f =ᵐ[volume.restrict (reflectedCell m z s R)]
      fun x => signLinear s (cubeProjectionVec (originCube d (1 - m)) k
        (fun y => f (y + auxCenter m z)) (reflectionChart m z s x)) := by
  have ha : ∀ᵐ x : Vec d ∂volume,
      auxAverage m (m + k) z f (reflectionChart m z s x + auxCenter m z) =
        cubeProjectionVec (originCube d (1 - m)) k (fun y => f (y + auxCenter m z))
          (reflectionChart m z s x) :=
    (measurePreserving_reflectionChart m z s).quasiMeasurePreserving.ae
      (auxAverage_add_eq_cubeProjectionVec_ae m k z f)
  have hm : MeasurableSet (reflectedCell m z s R) :=
    (isOpen_openCubeSet R).measurableSet.preimage (reflectionChart m z s).measurable
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_mem hm] with x hx hxR
  rw [reflectedAverage, reflectedGradient_eq_chart m z s _
    (reflectedCell_subset_of_mem_descendantsAtDepth m z s hR hxR), hx]

/-- Every reflected gradient increment cancels on each reflected parent cell. -/
theorem integral_reflectedAverage_increment_coordinate_eq_zero (m : ℤ)
    (z : Fin d → ℤ) (s : Fin d → Bool) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (1 - m)) j)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume) (i : Fin d) :
    ∫ x in reflectedCell m z s R,
      (reflectedAverage m (j + 1) z f x i - reflectedAverage m j z f x i) ∂volume = 0 := by
  let Q := originCube d (1 - m)
  let g := fun y => f (y + auxCenter m z)
  have heq : (fun x => reflectedAverage m (j + 1) z f x i - reflectedAverage m j z f x i)
      =ᵐ[volume.restrict (reflectedCell m z s R)]
      fun x => reflectionSign (s i) * (cubeProjectionVec Q (j + 1) g
        (reflectionChart m z s x) i - cubeProjectionVec Q j g (reflectionChart m z s x) i) := by
    filter_upwards [reflectedAverage_eq_projection_on_cell_ae m z s hR f (j + 1),
      reflectedAverage_eq_projection_on_cell_ae m z s hR f j] with x hn hp
    rw [hn, hp, signLinear_apply, signLinear_apply, mul_sub]
  rw [integral_congr_ae heq, integral_const_mul]
  rw [(measurePreserving_reflectionChart_restrict m z s R).integral_comp
    (reflectionChart m z s).measurableEmbedding
    (fun y => cubeProjectionVec Q (j + 1) g y i - cubeProjectionVec Q j g y i)]
  rw [← setIntegral_congr_set (cubeSet_ae_eq_openCubeSet R)]
  rw [integral_cubeProjectionVec_increment_coordinate_eq_zero g hR
    (integrableOn_auxCenter_pullback m z f hf) i, mul_zero]

end

end CoarseDeGiorgi.Foundations.Reconstruction
