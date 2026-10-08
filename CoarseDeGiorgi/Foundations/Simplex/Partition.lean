module

public import CoarseDeGiorgi.Foundations.Simplex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Data.Fintype.Perm

/-! # The Kuhn partition and its cell volumes

The exceptional set is the union of the translated coordinate diagonals.
Sorting gives coverage off those diagonals; uniqueness of sorted injective
tuples gives disjointness. Coordinate permutations make all cell volumes equal.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Simplex

open Homogenization Set MeasureTheory
open scoped ENNReal

theorem pairwise_disjoint_kuhnSimplex {d : ℕ} (n : ℤ) (z : Vec d) :
    Pairwise (fun π τ : Equiv.Perm (Fin d) =>
      Disjoint (kuhnSimplex n π z) (kuhnSimplex n τ z)) := by
  intro π τ hne
  apply disjoint_left.2
  intro x hx hy
  let f : Fin d → ℝ := fun i => x i - z i
  have hπ : StrictMono (f ∘ π) := hx.2
  have hτ : StrictMono (f ∘ τ) := hy.2
  have hf : Function.Injective f := by
    intro i j hij
    have h := hπ.injective (show (f ∘ π) (π.symm i) = (f ∘ π) (π.symm j) by
      simpa only [Function.comp_apply, π.apply_symm_apply] using hij)
    exact π.symm.injective h
  apply hne
  apply Equiv.ext
  intro i
  exact hf (congrFun (Tuple.unique_monotone hπ.monotone hτ.monotone) i)

theorem exists_mem_kuhnSimplex_of_injective {d : ℕ} (n : ℤ) (z x : Vec d)
    (hx : x ∈ simplexCube n z) (hf : Function.Injective (fun i => x i - z i)) :
    ∃ π : Equiv.Perm (Fin d), x ∈ kuhnSimplex n π z := by
  let f : Fin d → ℝ := fun i => x i - z i
  refine ⟨Tuple.sort f, hx, ?_⟩
  have hm := Tuple.monotone_sort f
  intro i j hij
  exact lt_of_le_of_ne (hm hij.le) (fun heq => hij.ne
    ((Tuple.sort f).injective (hf heq)))

theorem volume_coordinate_diagonal {d : ℕ} (z : Vec d) (i j : Fin d) (hij : i ≠ j) :
    volume {x : Vec d | x i - z i = x j - z j} = 0 := by
  let L : Vec d →ₗ[ℝ] ℝ := (LinearMap.proj i : Vec d →ₗ[ℝ] ℝ) -
    (LinearMap.proj j : Vec d →ₗ[ℝ] ℝ)
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hp : Pi.single i (1 : ℝ) ∈ LinearMap.ker L := by rw [h]; exact Submodule.mem_top
    have hji : j ≠ i := hij.symm
    simp only [LinearMap.mem_ker, L, LinearMap.sub_apply, LinearMap.proj_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hji, sub_zero, one_ne_zero] at hp
  have hnull := Measure.addHaar_submodule volume (LinearMap.ker L) hker
  have heq : {x : Vec d | x i - z i = x j - z j} =
      (fun x : Vec d => x + -z) ⁻¹' (LinearMap.ker L : Set (Vec d)) := by
    ext x
    change x i - z i = x j - z j ↔ (x + -z) i - (x + -z) j = 0
    simp only [Pi.add_apply, Pi.neg_apply, sub_eq_zero]
    simp only [sub_eq_add_neg]
  rw [heq, measure_preimage_add_right]
  exact hnull

theorem ae_injective_coordinates {d : ℕ} (z : Vec d) :
    ∀ᵐ x : Vec d ∂volume, Function.Injective (fun i => x i - z i) := by
  have hpair : ∀ i j : Fin d, ∀ᵐ x : Vec d ∂volume,
      x i - z i = x j - z j → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · apply ae_iff.2
      simpa only [hij, imp_false, not_not] using volume_coordinate_diagonal z i j hij
  exact (ae_all_iff.2 fun i => ae_all_iff.2 (hpair i))

theorem iUnion_kuhnSimplex_ae_eq_cube {d : ℕ} (n : ℤ) (z : Vec d) :
    (⋃ π : Equiv.Perm (Fin d), kuhnSimplex n π z) =ᵐ[volume] simplexCube n z := by
  filter_upwards [ae_injective_coordinates z] with x hx
  apply propext
  constructor
  · intro h
    obtain ⟨π, hπ⟩ := mem_iUnion.1 h
    exact hπ.1
  · intro h
    obtain ⟨π, hπ⟩ := exists_mem_kuhnSimplex_of_injective n z x h hx
    exact mem_iUnion.2 ⟨π, hπ⟩

theorem volume_kuhnSimplex_eq_volume_refl {d : ℕ} (n : ℤ)
    (π : Equiv.Perm (Fin d)) (z : Vec d) :
    volume (kuhnSimplex n π z) = volume (kuhnSimplex n (Equiv.refl (Fin d)) 0) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) π.symm
  have he (x : Vec d) (i : Fin d) : e x i = x (π i) := by
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have heq : kuhnSimplex n π z = (fun x : Vec d => x + -z) ⁻¹'
      (e ⁻¹' kuhnSimplex n (Equiv.refl _) 0) := by
    ext x
    simp only [kuhnSimplex, simplexCube, mem_ofPred_eq, mem_preimage, he,
      Pi.add_apply, Pi.neg_apply, Pi.zero_apply, Equiv.refl_apply,
      sub_eq_add_neg, neg_zero, add_zero]
    constructor
    · rintro ⟨hb, hm⟩
      exact ⟨fun i => hb (π i), hm⟩
    · rintro ⟨hb, hm⟩
      refine ⟨?_, hm⟩
      intro i
      simpa only [π.apply_symm_apply] using hb (π.symm i)
  rw [heq, measure_preimage_add_right]
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ) π.symm).measure_preimage_equiv _

theorem volume_simplexCube {d : ℕ} (n : ℤ) (z : Vec d) :
    volume (simplexCube n z) = ENNReal.ofReal ((3 : ℝ) ^ (n * (d : ℤ))) := by
  have heq : simplexCube n z = pi univ (fun i =>
      Ioo (z i - (3 : ℝ) ^ n / 2) (z i + (3 : ℝ) ^ n / 2)) := by
    ext x
    simp only [simplexCube, mem_ofPred_eq, mem_pi, mem_univ, mem_Ioo, true_implies]
    constructor <;> intro hx i <;> obtain ⟨hl, hu⟩ := hx i <;>
      constructor <;> linarith only [hl, hu]
  rw [heq, Real.volume_pi_Ioo]
  have hw (i : Fin d) : z i + (3 : ℝ) ^ n / 2 - (z i - (3 : ℝ) ^ n / 2) =
      (3 : ℝ) ^ n := by ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (zpow_pos (by norm_num) n).le, zpow_mul, zpow_natCast]

theorem factorial_mul_volume_kuhnSimplex {d : ℕ} (n : ℤ)
    (π : Equiv.Perm (Fin d)) (z : Vec d) :
    (d.factorial : ℝ≥0∞) * volume (kuhnSimplex n π z) =
      ENNReal.ofReal ((3 : ℝ) ^ (n * (d : ℤ))) := by
  have hsum := measure_iUnion (μ := volume) (pairwise_disjoint_kuhnSimplex n z)
    (fun π => (isOpen_kuhnSimplex n π z).measurableSet)
  rw [measure_congr (iUnion_kuhnSimplex_ae_eq_cube n z), volume_simplexCube] at hsum
  rw [tsum_fintype] at hsum
  simp_rw [volume_kuhnSimplex_eq_volume_refl] at hsum
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, volume_kuhnSimplex_eq_volume_refl n π z] using hsum.symm

theorem volume_kuhnSimplex {d : ℕ} (n : ℤ)
    (π : Equiv.Perm (Fin d)) (z : Vec d) :
    volume (kuhnSimplex n π z) =
      ENNReal.ofReal ((3 : ℝ) ^ (n * (d : ℤ))) / (d.factorial : ℝ≥0∞) := by
  apply (ENNReal.eq_div_iff (a := (d.factorial : ℝ≥0∞)) (by exact_mod_cast Nat.factorial_ne_zero d)
    (ENNReal.natCast_ne_top d.factorial)).2
  exact factorial_mul_volume_kuhnSimplex n π z

end CoarseDeGiorgi.Foundations.Simplex
