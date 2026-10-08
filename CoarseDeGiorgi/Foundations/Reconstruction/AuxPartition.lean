import CoarseDeGiorgi.Foundations.Reconstruction.AuxFaceClosure
import CoarseDeGiorgi.Foundations.Reconstruction.ProjectionL1
import Mathlib.Algebra.Ring.Parity

/-! # Exact offsets in the translated triadic partition -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators Topology

noncomputable section

variable {d : ℕ}

/-- Radius of the integer offset box at relative depth `j`. -/
def offsetRadius (j : ℕ) : ℤ := ((3 ^ j - 1) / 2 : ℕ)

theorem two_mul_offsetRadius_add_one (j : ℕ) :
    2 * offsetRadius j + 1 = (3 : ℤ) ^ j := by
  obtain ⟨a, ha⟩ := (show Odd (3 : ℕ) by decide).pow (n := j)
  have hdiv : (3 ^ j - 1) / 2 = a := by omega
  simp only [offsetRadius, hdiv]
  exact_mod_cast ha.symm

theorem mem_auxDescendantIndices_iff (m k : ℤ) (hmk : m ≤ k) (n : Fin d → ℤ) :
    n ∈ auxDescendantIndices m k ↔
      ∀ i, -offsetRadius (k - m).toNat ≤ n i ∧ n i ≤ offsetRadius (k - m).toNat := by
  classical
  unfold auxDescendantIndices
  simp only [dite_eq_left hmk, Finset.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    exact Finset.mem_Icc.mp ((Finset.mem_pi.mp hf) i (Finset.mem_univ i))
  · intro hn
    refine ⟨fun i _ => n i, ?_, rfl⟩
    exact Finset.mem_pi.mpr fun i _ => Finset.mem_Icc.mpr (hn i)

/-- The geometric side ratio agrees with the natural-depth scale. -/
theorem auxSide_eq_mul_pow (m k : ℤ) (hmk : m ≤ k) :
    auxSide m = auxSide k * (3 : ℝ) ^ (k - m).toNat := by
  rw [auxSide, auxSide, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hmk),
    ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  omega

/-- The unshifted descriptor of an auxiliary descendant. -/
def auxDescendantDescriptor (k : ℤ) (n : Fin d → ℤ) : TriadicCube d :=
  ⟨1 - k, n⟩

/-- An auxiliary open descendant is exactly a translated ordinary open cube. -/
theorem auxDescendantCube_eq_translate (m k : ℤ) (z n : Fin d → ℤ) :
    auxDescendantCube m k z n =
      (fun x => x + auxCenter m z) '' openCubeSet (auxDescendantDescriptor k n) := by
  ext x
  rw [Set.mem_image]
  constructor
  · intro hx
    refine ⟨x - auxCenter m z, ?_, sub_add_cancel _ _⟩
    intro i
    have hi := abs_lt.mp (hx i)
    dsimp [openCubeSet, auxDescendantDescriptor, cubeScaleFactor, auxCenter]
    constructor <;> linarith [hi.1, hi.2]
  · rintro ⟨y, hy, rfl⟩ i
    have hi := hy i
    dsimp [openCubeSet, auxDescendantDescriptor, cubeScaleFactor] at hi
    apply abs_lt.mpr
    dsimp [auxCenter]
    constructor <;> linarith [hi.1, hi.2]

/-- The exact offset range selects precisely the descendants of the translated root. -/
theorem auxDescendantDescriptor_mem_iff (m k : ℤ) (hmk : m ≤ k) (n : Fin d → ℤ) :
    auxDescendantDescriptor k n ∈ descendantsAtDepth (originCube d (1 - m))
        (k - m).toNat ↔ n ∈ auxDescendantIndices m k := by
  let j := (k - m).toNat
  let h := auxSide k
  have hh : 0 < h := auxSide_pos k
  have hratio : auxSide m = h * (3 : ℝ) ^ j := auxSide_eq_mul_pow m k hmk
  have hN : 2 * (offsetRadius j : ℝ) + 1 = (3 : ℝ) ^ j := by
    exact_mod_cast two_mul_offsetRadius_add_one j
  have hscale : (1 - m) - (j : ℤ) = 1 - k := by
    dsimp only [j]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hmk)]
    omega
  rw [mem_auxDescendantIndices_iff m k hmk]
  constructor
  · intro hmem i
    change -offsetRadius j ≤ n i ∧ n i ≤ offsetRadius j
    have hc : cubeCenter (auxDescendantDescriptor k n) ∈
        cubeSet (auxDescendantDescriptor k n) := by
      intro a
      change ((n a : ℝ) - 1 / 2) * h ≤ (n a : ℝ) * h ∧
        (n a : ℝ) * h < ((n a : ℝ) + 1 / 2) * h
      constructor <;> nlinarith
    have hi := cubeSet_subset_of_mem_descendantsAtDepth hmem hc i
    simp only [originCube, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add] at hi
    change -(1 / 2 : ℝ) * auxSide m ≤ (n i : ℝ) * h ∧
      (n i : ℝ) * h < (1 / 2 : ℝ) * auxSide m at hi
    rw [hratio, ← hN] at hi
    have hlo : -(offsetRadius j : ℝ) - 1 / 2 ≤ (n i : ℝ) := by
      nlinarith [hi.1]
    have hhi : (n i : ℝ) < (offsetRadius j : ℝ) + 1 / 2 := by
      nlinarith [hi.2]
    have hlo' : -(2 * offsetRadius j + 1) ≤ 2 * n i := by exact_mod_cast (by linarith :
      -(2 * (offsetRadius j : ℝ) + 1) ≤ 2 * (n i : ℝ))
    have hhi' : 2 * n i < 2 * offsetRadius j + 1 := by exact_mod_cast (by linarith :
      2 * (n i : ℝ) < 2 * (offsetRadius j : ℝ) + 1)
    constructor <;> omega
  · intro hn
    have hcenter : cubeCenter (auxDescendantDescriptor k n) ∈
        cubeSet (originCube d (1 - m)) := by
      intro i
      have hlo : -(offsetRadius j : ℝ) ≤ (n i : ℝ) := by exact_mod_cast (hn i).1
      have hhi : (n i : ℝ) ≤ (offsetRadius j : ℝ) := by exact_mod_cast (hn i).2
      simp only [originCube, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
      change -(1 / 2 : ℝ) * auxSide m ≤ (n i : ℝ) * h ∧
        (n i : ℝ) * h < (1 / 2 : ℝ) * auxSide m
      rw [hratio, ← hN]
      constructor <;> nlinarith
    obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hcenter
    have hRs : R.scale = 1 - k :=
      (scale_eq_sub_of_mem_descendantsAtDepth hR).trans hscale
    have hRi : R.index = n := by
      funext i
      have hi := hxR i
      change ((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale ≤ (n i : ℝ) * h ∧
        (n i : ℝ) * h < ((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale at hi
      rw [hRs] at hi
      change ((R.index i : ℝ) - 1 / 2) * h ≤ (n i : ℝ) * h ∧
        (n i : ℝ) * h < ((R.index i : ℝ) + 1 / 2) * h at hi
      have hlo := (mul_le_mul_iff_left₀ hh).mp hi.1
      have hhi := (mul_lt_mul_iff_left₀ hh).mp hi.2
      have hlo' : 2 * R.index i - 1 ≤ 2 * n i := by exact_mod_cast (by linarith :
        2 * (R.index i : ℝ) - 1 ≤ 2 * (n i : ℝ))
      have hhi' : 2 * n i < 2 * R.index i + 1 := by exact_mod_cast (by linarith :
        2 * (n i : ℝ) < 2 * (R.index i : ℝ) + 1)
      omega
    have heq : R = auxDescendantDescriptor k n := by
      cases R
      simp_all [auxDescendantDescriptor]
    exact heq ▸ hR

/-- The descriptor map is injective because it keeps every integer offset. -/
def auxDescriptorEmbedding (k : ℤ) : (Fin d → ℤ) ↪ TriadicCube d where
  toFun := auxDescendantDescriptor k
  inj' := fun _ _ h => congrArg TriadicCube.index h

theorem descendantsAtDepth_eq_map_auxDescendantIndices (m k : ℤ) (hmk : m ≤ k) :
    descendantsAtDepth (originCube d (1 - m)) (k - m).toNat =
      (auxDescendantIndices m k).map (auxDescriptorEmbedding k) := by
  classical
  ext R
  rw [Finset.mem_map]
  constructor
  · intro hR
    have hs : R.scale = 1 - k := by
      have hs := scale_eq_sub_of_mem_descendantsAtDepth hR
      dsimp [originCube] at hs
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hmk)] at hs
      omega
    have heq : auxDescendantDescriptor k R.index = R := by
      cases R
      simp_all [auxDescendantDescriptor]
    refine ⟨R.index, ?_, heq⟩
    apply (auxDescendantDescriptor_mem_iff m k hmk R.index).mp
    exact heq.symm ▸ hR
  · rintro ⟨n, hn, rfl⟩
    exact (auxDescendantDescriptor_mem_iff m k hmk n).mpr hn

end

end CoarseDeGiorgi.Foundations.Reconstruction
