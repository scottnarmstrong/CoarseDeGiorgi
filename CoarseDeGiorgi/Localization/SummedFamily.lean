module

public import CoarseDeGiorgi.Localization.SummedConverge
public import CoarseDeGiorgi.Localization.SummedBound
public import CoarseDeGiorgi.Localization.SummedCongr
public import CoarseDeGiorgi.Statements.IsFractionalCover
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.SelectionInterval

/-! # The covers and partitions of the localization, chosen from the radii alone

Used in the proof of Proposition `p.fractional.localization`. -/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem isOpen_originCube (R : ℝ) : IsOpen (originCube (d := d) R) := by
  rw [← radiusCube_eq_originCube]
  simp only [radiusCube, ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i |>.abs) continuous_const

/-- A scale `m` adapted to the compact set `K` and the radii `ρ₁ < ρ₂`. -/
def GoodLevel (K : Set (Vec d)) (ρ₁ ρ₂ : ℝ) (m : ℤ) : Prop :=
  (ρ₂ - ρ₁) / 192 < gridSpacing m ∧ gridSpacing m ≤ (ρ₂ - ρ₁) / 64 ∧
    LocalizationCover m K ρ₂ (ρ₂ - ρ₁) ∧
    ∃ b : ℝ, (∀ y ∈ K, ∀ i, |y i| ≤ b / 2) ∧ b + 4 * gridSpacing m < ρ₂

theorem exists_goodLevel_annulus {ρ₁ ρ₂ : ℝ} (h1 : 1 / 2 ≤ ρ₁) (h12 : ρ₁ < ρ₂) (h2 : ρ₂ ≤ 1) :
    ∃ m, GoodLevel (localizationAnnulus (d := d) ρ₁ ρ₂) ρ₁ ρ₂ m := by
  have hδ : 0 < ρ₂ - ρ₁ := sub_pos.mpr h12
  obtain ⟨m, -, hslo, hshi⟩ := exists_localization_scale hδ (by linarith)
  have hK : ∀ y ∈ localizationAnnulus (d := d) ρ₁ ρ₂, ∀ i, |y i| ≤ (ρ₁ + 5 * (ρ₂ - ρ₁) / 8) / 2 := by
    intro y hy i
    have hi : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
    have hu := hy.2
    linarith only [hi, hu]
  refine ⟨m, hslo, hshi, ?_, ρ₁ + 5 * (ρ₂ - ρ₁) / 8, hK, annular_margin h12 hshi⟩
  exact localizationCover_of_coordinate_bounds hδ (by linarith only [hshi, h1, h2]) hslo hK
    (by linarith only [h12, h2]) (annular_margin h12 hshi)

theorem exists_goodLevel_inner {ρ₁ ρ₂ : ℝ} (h1 : 1 / 2 ≤ ρ₁) (h12 : ρ₁ < ρ₂) (h2 : ρ₂ ≤ 1) :
    ∃ m, GoodLevel {x : Vec d | ∀ i, |x i| ≤ ρ₁ / 2} ρ₁ ρ₂ m := by
  have hδ : 0 < ρ₂ - ρ₁ := sub_pos.mpr h12
  obtain ⟨m, -, hslo, hshi⟩ := exists_localization_scale hδ (by linarith)
  exact ⟨m, hslo, hshi, localizationCover_of_coordinate_bounds hδ (by linarith only [hshi, h1, h2]) hslo
    (fun _ hx => hx) (h12.le.trans h2) (inner_margin h12 hshi), ρ₁, fun _ hx => hx,
    inner_margin h12 hshi⟩

/-- The chosen scale and cover indices (junk values for inadmissible radii). -/
def chosenLevel (Kf : ℝ → ℝ → Set (Vec d)) (ρ₁ ρ₂ : ℝ) : ℤ :=
  if h : ∃ m, GoodLevel (Kf ρ₁ ρ₂) ρ₁ ρ₂ m then h.choose else 0

def chosenIndices (Kf : ℝ → ℝ → Set (Vec d)) (ρ₁ ρ₂ : ℝ) : Finset (Fin d → ℤ) :=
  if h : ∃ m, GoodLevel (Kf ρ₁ ρ₂) ρ₁ ρ₂ m then coverIndices h.choose (Kf ρ₁ ρ₂) else ∅

def chosenS (Kf : ℝ → ℝ → Set (Vec d)) (ρ₁ ρ₂ : ℝ) : Finset (ℤ × (Fin d → ℤ)) :=
  (chosenIndices Kf ρ₁ ρ₂).image fun z => (chosenLevel Kf ρ₁ ρ₂, z)

def chosenPhi (Kf : ℝ → ℝ → Set (Vec d)) (ρ₁ ρ₂ : ℝ) (i : ℤ × (Fin d → ℤ)) (x : Vec d) : ℝ :=
  localizationPartition (chosenLevel Kf ρ₁ ρ₂) (chosenIndices Kf ρ₁ ρ₂) i.2 x

theorem chosen_spec {Kf : ℝ → ℝ → Set (Vec d)} {ρ₁ ρ₂ : ℝ}
    (h : ∃ m, GoodLevel (Kf ρ₁ ρ₂) ρ₁ ρ₂ m) :
    GoodLevel (Kf ρ₁ ρ₂) ρ₁ ρ₂ (chosenLevel Kf ρ₁ ρ₂) ∧
      chosenIndices Kf ρ₁ ρ₂ = coverIndices (chosenLevel Kf ρ₁ ρ₂) (Kf ρ₁ ρ₂) := by
  unfold chosenLevel chosenIndices
  simp only [h, ↓reduceDIte]
  exact ⟨h.choose_spec, trivial⟩

theorem sum_chosenS (Kf : ℝ → ℝ → Set (Vec d)) (ρ₁ ρ₂ : ℝ) (v : Vec d → ℝ) (x : Vec d) :
    (∑ i ∈ chosenS Kf ρ₁ ρ₂, chosenPhi Kf ρ₁ ρ₂ i x * v x) =
      localizedFunction (chosenLevel Kf ρ₁ ρ₂) (chosenIndices Kf ρ₁ ρ₂) v x := by
  unfold chosenS localizedFunction chosenPhi
  rw [Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.mp h).2)]

theorem tsupport_partition_subset_auxCube (m : ℤ) (Z : Finset (Fin d → ℤ)) (z : Fin d → ℤ) :
    tsupport (localizationPartition m Z z) ⊆ auxCube m z := by
  intro x hx
  by_contra hn
  have h := localizationPartition_separation hx hn
  rw [Foundations.Euclid.eDist2_self] at h
  exact (not_le_of_gt (half_pos (gridSpacing_pos m))) h

theorem chosen_isFractionalCover {Kf : ℝ → ℝ → Set (Vec d)} {ρ₁ ρ₂ : ℝ}
    (h : ∃ m, GoodLevel (Kf ρ₁ ρ₂) ρ₁ ρ₂ m) :
    IsFractionalCover ρ₂ (chosenS Kf ρ₁ ρ₂) (chosenPhi Kf ρ₁ ρ₂) := by
  obtain ⟨⟨-, -, hcover, -⟩, hZ⟩ := chosen_spec h
  intro i hi
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
  rw [hZ] at hz
  have hcl := hcover.1 z hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [radiusCube_eq_originCube] using hcl.2
  · exact contDiff_localizationPartition _ _ _
  · exact hcl.1.of_isClosed_subset isClosed_closure
      ((tsupport_partition_subset_auxCube _ _ _).trans subset_closure)
  · exact tsupport_partition_subset_auxCube _ _ _
  · exact fun x => localizationPartition_nonneg _ _ _ x

theorem localizedFunction_ae_eq {m : ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : ∀ z ∈ Z, auxCube m z ⊆ originCube 1) {w w' : Vec d → ℝ}
    (h : w =ᵐ[volume.restrict (originCube 1)] w') :
    localizedFunction m Z w =ᵐ[volume] localizedFunction m Z w' := by
  have h' := (ae_restrict_iff' (isOpen_originCube (d := d) 1).measurableSet).mp h
  filter_upwards [h'] with x hx
  unfold localizedFunction
  refine Finset.sum_congr rfl fun z hz => ?_
  by_cases h0 : localizationPartition m Z z x = 0
  · rw [h0, zero_mul, zero_mul]
  · have := hZ z hz (support_partition_subset_auxCube m Z z h0)
    rw [hx this]

end
end CoarseDeGiorgi.Localization
