module

public import CoarseDeGiorgi.Foundations.Reconstruction.CubeCutoffL1
public import Homogenization.Geometry.Translation
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Face-zero weak identities on the exact auxiliary cube -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Centre of the root auxiliary cube, independently of the centered triadic lattice. -/
def auxCenter (m : ℤ) (z : Fin d → ℤ) : Vec d :=
  fun i => (z i : ℝ) * (3 : ℝ) ^ (-m)

/-- The auxiliary root is a translated origin cube, with its exact absolute scale. -/
theorem auxCube_eq_translate_originCube (m : ℤ) (z : Fin d → ℤ) :
    auxCube m z = translateSet (auxCenter m z) (openCubeSet (originCube d (1 - m))) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  simp only [auxCube, openCubeSet, originCube, cubeScaleFactor, Pi.zero_apply,
    Int.cast_zero, Set.mem_ofPred_eq, Pi.sub_apply]
  change (∀ i, |x i - auxCenter m z i| < auxSide m / 2) ↔
    (∀ i, ((0 : ℝ) - 1 / 2) * auxSide m < x i - auxCenter m z i ∧
      x i - auxCenter m z i < ((0 : ℝ) + 1 / 2) * auxSide m)
  simp only [abs_lt]
  constructor <;> intro h i <;> specialize h i <;> constructor <;> linarith only [h.1, h.2]

/-- Translation pulls back the exact weak partial derivative without an integrability premise. -/
theorem weakPartial_pullback_add {U : Set (Vec d)} {i : Fin d} {c : Vec d}
    {w gi : Vec d → ℝ} (h : HasWeakPartialDerivOn (translateSet c U) i w gi) :
    HasWeakPartialDerivOn U i (fun x => w (x + c)) (fun x => gi (x + c)) := by
  intro φ hφ hcompact hsupp
  let ψ : Vec d → ℝ := fun x => φ (x - c)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.sub contDiff_const)
  have hc : HasCompactSupport ψ := hcompact.comp_homeomorph (Homeomorph.subRight c)
  have hs : tsupport ψ ⊆ translateSet c U := by
    intro x hx
    have hxφ : x - c ∈ tsupport φ := by
      change x ∈ tsupport (φ ∘ Homeomorph.subRight c) at hx
      rw [tsupport_comp_eq_preimage] at hx
      exact hx
    exact mem_translateSet_iff_sub_mem.mpr (hsupp hxφ)
  have ht := h ψ hψ hc hs
  have hd (x : Vec d) : fderiv ℝ ψ (x + c) = fderiv ℝ φ x := by
    change fderiv ℝ (fun y => φ (y - c)) (x + c) = _
    rw [fderiv_comp_sub, add_sub_cancel_right]
  have hleft := setIntegral_comp_addRight_translateSet c U
    (fun x => w x * (fderiv ℝ ψ x) (basisVec i))
  have hright := setIntegral_comp_addRight_translateSet c U (fun x => gi x * ψ x)
  calc
    ∫ x in U, w (x + c) * (fderiv ℝ φ x) (basisVec i) ∂volume =
        ∫ x in U, w (x + c) * (fderiv ℝ ψ (x + c)) (basisVec i) ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [hd x]
    _ = ∫ x in translateSet c U, w x * (fderiv ℝ ψ x) (basisVec i) ∂volume := hleft
    _ = -∫ x in translateSet c U, gi x * ψ x ∂volume := ht
    _ = -∫ x in U, gi (x + c) * φ x ∂volume := by
      rw [← hright]
      simp only [ψ, add_sub_cancel_right]

/-- Face-zero closure transported to an arbitrary translate of a triadic cube. -/
theorem weakPartial_integral_translated_face_zero (Q : TriadicCube d) (c : Vec d)
    (i : Fin d) {w gi ψ : Vec d → ℝ}
    (hweak : HasWeakPartialDerivOn (translateSet c (openCubeSet Q)) i w gi)
    (hw : IntegrableOn w (translateSet c (openCubeSet Q)) volume)
    (hgi : IntegrableOn gi (translateSet c (openCubeSet Q)) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hlower : ∀ x, ψ (cubeLowerFaceProjection Q i x + c) = 0)
    (hupper : ∀ x, ψ (cubeUpperFaceProjection Q i x + c) = 0) :
    ∫ x in translateSet c (openCubeSet Q), w x * (fderiv ℝ ψ x) (basisVec i) ∂volume =
      -∫ x in translateSet c (openCubeSet Q), gi x * ψ x ∂volume := by
  have hμ := measurePreserving_addRight_restrict_translateSet c (openCubeSet Q)
  have hw' : IntegrableOn (fun x => w (x + c)) (openCubeSet Q) volume :=
    (hμ.integrable_comp_emb (Homeomorph.addRight c).measurableEmbedding).mpr hw
  have hgi' : IntegrableOn (fun x => gi (x + c)) (openCubeSet Q) volume :=
    (hμ.integrable_comp_emb (Homeomorph.addRight c).measurableEmbedding).mpr hgi
  have ht := weakPartial_integral_face_zero_of_contDiff Q i
    (weakPartial_pullback_add hweak) hw' hgi'
    (hψ.comp (contDiff_id.add contDiff_const)) hlower hupper
  have hd (x : Vec d) : fderiv ℝ (fun y => ψ (y + c)) x = fderiv ℝ ψ (x + c) :=
    fderiv_comp_add_right c
  change (∫ x in openCubeSet Q, w (x + c) *
    (fderiv ℝ (fun y => ψ (y + c)) x) (basisVec i) ∂volume) =
    -∫ x in openCubeSet Q, gi (x + c) * ψ (x + c) ∂volume at ht
  simp only [hd] at ht
  rw [setIntegral_comp_addRight_translateSet c (openCubeSet Q)
    (fun x => w x * (fderiv ℝ ψ x) (basisVec i)),
    setIntegral_comp_addRight_translateSet c (openCubeSet Q) (fun x => gi x * ψ x)] at ht
  exact ht

/-- The original-domain folded weak identity with the cutoff completely removed.
The only field assumptions are exactly the L¹ assumptions of reconstruction. -/
theorem weakGradient_folded_identity {m : ℤ} {z : Fin d → ℤ}
    {w : Vec d → ℝ} {Dw : Vec d → Vec d}
    (hweak : HasWeakGradientOn (auxCube m z) w Dw)
    (hw : IntegrableOn w (auxCube m z) volume)
    (hDw : IntegrableOn Dw (auxCube m z) volume) (i : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hperiod : ∀ y, φ (y + (2 * auxSide m) • basisVec i) = φ y) :
    ∫ x in auxCube m z, w x * ∑ s : Fin d → Bool,
      (fderiv ℝ φ (signLinear s (x - auxLower m z))) (basisVec i) ∂volume =
      -∫ x in auxCube m z, Dw x i * translatedFoldedTest m z i φ x ∂volume := by
  let Q := originCube d (1 - m)
  have hlow (x : Vec d) :
      (cubeLowerFaceProjection Q i x + auxCenter m z - auxLower m z) i = 0 := by
    simp only [cubeLowerFaceProjection, Function.update_self, Pi.add_apply, Pi.sub_apply,
      cubeLowerFaceCoord, Q, originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub,
      auxCenter, auxLower, auxSide]
    ring
  have hupp (x : Vec d) :
      (cubeUpperFaceProjection Q i x + auxCenter m z - auxLower m z) i = auxSide m := by
    simp only [cubeUpperFaceProjection, Function.update_self, Pi.add_apply, Pi.sub_apply,
      cubeUpperFaceCoord, Q, originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_add,
      auxCenter, auxLower, auxSide]
    ring
  have ht := weakPartial_integral_translated_face_zero Q (auxCenter m z) i
    (w := w) (gi := fun x => Dw x i) (ψ := translatedFoldedTest m z i φ)
    (by simpa only [Q, ← auxCube_eq_translate_originCube] using hweak i)
    (by simpa only [Q, ← auxCube_eq_translate_originCube] using hw)
    (by simpa only [Q, ← auxCube_eq_translate_originCube] using (show IntegrableOn (fun x => Dw x i) (auxCube m z) volume from hDw.eval i))
    (contDiff_translatedFoldedTest m z i hφ)
    (fun x => foldedTest_eq_zero_of_lower_face i φ _ (hlow x))
    (fun x => foldedTest_eq_zero_of_upper_face i φ hperiod _ (hupp x))
  simpa only [Q, ← auxCube_eq_translate_originCube, fderiv_translatedFoldedTest_basisVec m z i hφ]
    using ht

end

end CoarseDeGiorgi.Foundations.Reconstruction
