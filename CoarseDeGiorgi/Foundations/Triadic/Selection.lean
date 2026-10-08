module

public import CoarseDeGiorgi.Foundations.Triadic.Distance
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization

noncomputable section

variable {d : ℕ}

/-- A maximal admissible cube, detected by its immediate parent. -/
def Selected (τ : ℝ) (D : TriadicCube d) : Prop :=
  Admissible τ D ∧ ¬Admissible τ (parentCube D)

/-- Maximality among all admissible triadic cubes under closed-cube inclusion. -/
def MaximalAdmissible (τ : ℝ) (D : TriadicCube d) : Prop :=
  Admissible τ D ∧ ∀ E : TriadicCube d,
    Admissible τ E → closedCube D ⊆ closedCube E → E = D

theorem selected_iff_maximalAdmissible {τ : ℝ} (hτ : 0 ≤ τ) (D : TriadicCube d) :
    Selected τ D ↔ MaximalAdmissible τ D := by
  constructor
  · rintro ⟨hD, hparent⟩
    refine ⟨hD, ?_⟩
    intro E hE hsub
    obtain ⟨i, _⟩ := (admissible_iff τ hτ D).mp hD
    have hi := (closedCube_subset_iff D E).mp hsub i
    have hfac : cubeScaleFactor D ≤ cubeScaleFactor E := by
      linarith only [hi, abs_nonneg (center D i - center E i)]
    have hs : D.scale ≤ E.scale :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hfac
    by_cases heq : D.scale = E.scale
    · exact (eq_of_scale_eq_of_overlap D E heq (center_mem_openCubeSet D)
        (center_mem_openCubeSet_of_subset D E hsub)).symm
    have hp : (parentCube D).scale ≤ E.scale := by
      rw [parentCube_scale]
      omega
    have hpsub : closedCube (parentCube D) ⊆ closedCube E := by
      rcases closedCube_subset_or_openCubeSet_disjoint (parentCube D) E hp with h | h
      · exact h
      · exact False.elim (Set.disjoint_left.mp h
          (center_mem_openCubeSet_of_subset D (parentCube D) (closedCube_subset_parent D))
          (center_mem_openCubeSet_of_subset D E hsub))
    exact False.elim (hparent (hE.of_subset hp hpsub))
  · rintro ⟨hD, hmax⟩
    refine ⟨hD, ?_⟩
    intro hp
    have heq := hmax (parentCube D) hp (closedCube_subset_parent D)
    have hs := congrArg TriadicCube.scale heq
    rw [parentCube_scale] at hs
    omega

theorem ancestor_scaleFactor (D : TriadicCube d) (n : ℕ) :
    cubeScaleFactor (ancestor D n) = (3 : ℝ) ^ n * cubeScaleFactor D := by
  rw [cubeScaleFactor, ancestor_scale, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
    zpow_natCast]
  exact mul_comm _ _

theorem exists_large_ancestor (D : TriadicCube d) (R : ℝ) :
    ∃ n : ℕ, R < cubeScaleFactor (ancestor D n) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / cubeScaleFactor D)
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_⟩
  rw [ancestor_scaleFactor]
  exact (div_lt_iff₀ (scaleFactor_pos D)).mp hn

theorem exists_selected_ancestor {τ : ℝ} (hτ : 0 ≤ τ)
    {D : TriadicCube d} (hD : Admissible τ D) :
    ∃ n : ℕ, Selected τ (ancestor D n) := by
  classical
  let x := center D
  obtain ⟨n, hn⟩ := exists_large_ancestor D (‖x‖ + 1)
  have hex : ∃ n : ℕ, ¬Admissible τ (ancestor D n) :=
    ⟨n, large_cube_not_admissible hτ (ancestor D n)
      (closedCube_subset_ancestor D n (center_mem_closedCube D)) hn⟩
  have hpos : 0 < Nat.find hex := by
    by_contra h
    have heq : Nat.find hex = 0 := by omega
    have hf := Nat.find_spec hex
    rw [heq] at hf
    exact hf hD
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact Classical.not_not.mp (Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex))
  · have hf := Nat.find_spec hex
    rw [← hsucc, ancestor] at hf
    exact hf

theorem exists_selected_closedCube {τ : ℝ} (hτ : 0 ≤ τ) {x : Vec d}
    (hx : x ∉ referenceCube τ) :
    ∃ D : TriadicCube d, Selected τ D ∧ x ∈ closedCube D := by
  obtain ⟨D, hxD, _, hD⟩ := exists_arbitrarily_small_admissible hτ hx
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨n, hn⟩ := exists_selected_ancestor hτ hD
  exact ⟨ancestor D n, hn, closedCube_subset_ancestor D n hxD⟩

theorem Selected.openCubeSet_disjoint {τ : ℝ} (hτ : 0 ≤ τ)
    {D E : TriadicCube d} (hD : Selected τ D) (hE : Selected τ E) (hne : D ≠ E) :
    Disjoint (Homogenization.openCubeSet D) (Homogenization.openCubeSet E) := by
  rcases nested_or_disjoint D E with ⟨_, _, hsub⟩ | ⟨_, _, hsub⟩ | hdis
  · have heq := ((selected_iff_maximalAdmissible hτ D).mp hD).2 E hE.1 hsub
    exact False.elim (hne heq.symm)
  · have heq := ((selected_iff_maximalAdmissible hτ E).mp hE).2 D hD.1 hsub
    exact False.elim (hne heq)
  · exact hdis

theorem Selected.distance_chain {τ : ℝ} (hτ : 0 ≤ τ) {D : TriadicCube d}
    (hD : Selected τ D) {x : Vec d} (hx : x ∈ closedCube D) :
    2 * cubeScaleFactor D < cubeInfDist τ D ∧
      cubeInfDist τ D ≤ Metric.infDist x (referenceCube τ) ∧
      Metric.infDist x (referenceCube τ) ≤ 9 * cubeScaleFactor D :=
  CoarseDeGiorgi.Foundations.Triadic.distance_chain hτ hD.1 hD.2 hx

end

end CoarseDeGiorgi.Foundations.Triadic
