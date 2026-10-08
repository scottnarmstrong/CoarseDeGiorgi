import CoarseDeGiorgi.Weighted.Energy
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The weighted energy respects equality almost everywhere. -/
theorem energy_congr_ae {G H : Vec d → Vec d}
    (h : G =ᵐ[volume.restrict V] H) : weightedEnergy a V G = weightedEnergy a V H := by
  apply lintegral_congr_ae
  exact h.mono fun x hx => by dsimp only; rw [hx]

/-- Measurable fields whose literal quadratic energy is integrable. -/
noncomputable def finiteEnergySubmodule (ha : IsWeightedCoeffOn V a) :
    Submodule ℝ (Vec d → Vec d) where
  carrier := {G | AEStronglyMeasurable G (volume.restrict V) ∧
    IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) V}
  zero_mem' := by
    refine ⟨aestronglyMeasurable_zero, ?_⟩
    simp [vecDot, matVecMul]
  add_mem' := by
    intro G H hG hH
    refine ⟨hG.1.add hH.1, quadratic_integrable ha (hG.1.add hH.1) ?_⟩
    apply energy_add_lt_top ha hG.1 hH.1
    · exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
        (quadratic_aestronglyMeasurable ha hG.1) (quadratic_nonneg ha G)).mpr hG.2)
    · exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
        (quadratic_aestronglyMeasurable ha hH.1) (quadratic_nonneg ha H)).mpr hH.2)
  smul_mem' := by
    intro c G hG
    refine ⟨hG.1.const_smul c, ?_⟩
    change Integrable _ (volume.restrict V)
    simpa only [Pi.smul_apply, matVecMul_smul, vecDot_smul_left,
      vecDot_smul_right, mul_assoc] using hG.2.const_mul (c * c)

/-- Raw finite-energy representatives; its energy seminorm ignores null sets. -/
noncomputable def GradientCore (ha : IsWeightedCoeffOn V a) := ↥(finiteEnergySubmodule ha)

noncomputable instance (ha : IsWeightedCoeffOn V a) : AddCommGroup (GradientCore ha) :=
  inferInstanceAs (AddCommGroup ↥(finiteEnergySubmodule ha))

noncomputable instance (ha : IsWeightedCoeffOn V a) : Module ℝ (GradientCore ha) :=
  inferInstanceAs (Module ℝ ↥(finiteEnergySubmodule ha))

namespace GradientCore

variable (ha : IsWeightedCoeffOn V a)

/-- The measurable representative of a raw energy element. -/
def field {ha : IsWeightedCoeffOn V a} (G : GradientCore ha) : Vec d → Vec d := G.1

@[simp] theorem field_sub (G H : GradientCore ha) : (G - H).field = G.field - H.field := rfl

theorem measurable (G : GradientCore ha) :
    AEStronglyMeasurable G.field (volume.restrict V) := G.2.1

theorem quadratic_integrable (G : GradientCore ha) :
    IntegrableOn (fun x => vecDot (G.field x) (matVecMul (a x) (G.field x))) V := G.2.2

theorem energy_lt_top (G : GradientCore ha) : weightedEnergy a V G.field < ⊤ :=
  lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
    (quadratic_aestronglyMeasurable ha (measurable ha G))
    (quadratic_nonneg ha G.field)).mpr (quadratic_integrable ha G))

noncomputable instance preInner : PreInnerProductSpace.Core ℝ (GradientCore ha) where
  inner G H := ∫ x in V, vecDot (G.field x) (matVecMul (a x) (H.field x))
  conj_inner_symm G H := by
    simp only [RCLike.conj_to_real]
    apply integral_congr_ae
    filter_upwards [ha.2.1] with x hx
    exact vecDot_matVecMul_comm_of_isSymm
      (by simpa [Matrix.IsSymm, Matrix.IsHermitian] using hx.1) _ _
  re_inner_nonneg G := by
    simp only [RCLike.re_to_real]
    exact integral_nonneg_of_ae (quadratic_nonneg ha G.field)
  add_left G H K := by
    change (∫ x in V, vecDot (G.field x + H.field x) (matVecMul (a x) (K.field x))) = _
    simp only [vecDot_add_left]
    exact integral_add
      (pairing_integrable_and_bound ha (measurable ha G) (measurable ha K)
        (energy_lt_top ha G) (energy_lt_top ha K)).1
      (pairing_integrable_and_bound ha (measurable ha H) (measurable ha K)
        (energy_lt_top ha H) (energy_lt_top ha K)).1
  smul_left G H c := by
    change (∫ x in V, vecDot (c • G.field x) (matVecMul (a x) (H.field x))) = _
    simp only [vecDot_smul_left, RCLike.conj_to_real]
    exact integral_const_mul c _

noncomputable instance seminormed : SeminormedAddCommGroup (GradientCore ha) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

noncomputable instance normedSpace : NormedSpace ℝ (GradientCore ha) :=
  InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ)

noncomputable instance innerProduct : InnerProductSpace ℝ (GradientCore ha) :=
  InnerProductSpace.ofCore (preInner ha)

/-- The seminorm has exactly the weighted energy, with no value term. -/
theorem norm_sq (G : GradientCore ha) : ‖G‖ ^ 2 = (weightedEnergy a V G.field).toReal := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ)]
  exact (energy_toReal ha (measurable ha G)).symm

end GradientCore

/-- Shared Hilbert ambient space for full and zero-boundary weighted Sobolev spaces. -/
abbrev GradientHilbert (ha : IsWeightedCoeffOn V a) :=
  UniformSpace.Completion (GradientCore ha)

/-- The energy pairing is preserved under the map into the Hilbert completion. -/
theorem gradientHilbert_inner_coe (ha : IsWeightedCoeffOn V a)
    (G H : GradientCore ha) :
    inner ℝ (G : GradientHilbert ha) (H : GradientHilbert ha) =
      ∫ x in V, vecDot (G.field x) (matVecMul (a x) (H.field x)) :=
  UniformSpace.Completion.inner_coe G H

end CoarseDeGiorgi.Weighted
