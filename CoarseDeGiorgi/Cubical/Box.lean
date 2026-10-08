module

public import CoarseDeGiorgi.Statements.CubeCell
public import CoarseDeGiorgi.Statements.GridOffset
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Moments.CubeCells
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Triadic cells as explicit boxes -/

@[expose] public section

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- The open triadic box of level `j` with integer index `z` in `(-1/2, 1/2)^d`. -/
def box (j : ℕ) (z : Fin d → ℕ) : Set (Vec d) :=
  {x | ∀ i, (z i : ℝ) / 3 ^ j - 1 / 2 < x i ∧ x i < ((z i : ℝ) + 1) / 3 ^ j - 1 / 2}

theorem cubeCell_eq_box (j : ℕ) (z : Fin d → Fin (3 ^ j)) :
    cubeCell j z = box j (fun i => (z i : ℕ)) := by
  have hodd : Odd (3 ^ j : ℕ) := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow
  obtain ⟨t, ht⟩ := hodd
  have hg : (3 ^ j - 1) / 2 = t := by omega
  have ht' : ((3 : ℝ) ^ j) = 2 * t + 1 := by exact_mod_cast ht
  have hpos : (0 : ℝ) < 3 ^ j := by positivity
  ext x
  simp only [cubeCell, originCube, box, Set.mem_ofPred_eq, gridOffset, hg, Pi.sub_apply]
  have hu : ((3 : ℝ) ^ (-(j : ℤ))) = ((3 : ℝ) ^ j)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [hu]
  refine forall_congr' fun i => ?_
  push_cast
  have h1 : (z i : ℝ) / 3 ^ j = ((3 : ℝ) ^ j)⁻¹ * z i := by ring
  have h2 : ((z i : ℝ) + 1) / 3 ^ j = ((3 : ℝ) ^ j)⁻¹ * z i + ((3 : ℝ) ^ j)⁻¹ := by ring
  have h3 : ((3 : ℝ) ^ j)⁻¹ * (2 * t + 1) = 1 := by rw [← ht']; exact inv_mul_cancel₀ hpos.ne'
  rw [h1, h2]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> nlinarith [h3]

theorem isOpen_box (j : ℕ) (z : Fin d → ℕ) : IsOpen (box j z) := by
  have : box j z = ⋂ i, ({x : Vec d | (z i : ℝ) / 3 ^ j - 1 / 2 < x i} ∩
      {x : Vec d | x i < ((z i : ℝ) + 1) / 3 ^ j - 1 / 2}) := by
    ext x; simp [box, forall_and]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

theorem measurableSet_box (j : ℕ) (z : Fin d → ℕ) : MeasurableSet (box j z) :=
  (isOpen_box j z).measurableSet

theorem box_nonempty (j : ℕ) (z : Fin d → ℕ) : (box j z).Nonempty := by
  have hpos : (0 : ℝ) < 3 ^ j := by positivity
  refine ⟨fun i => ((z i : ℝ) + 1 / 2) / 3 ^ j - 1 / 2, fun i => ?_⟩
  constructor
  · have : (z i : ℝ) / 3 ^ j < ((z i : ℝ) + 1 / 2) / 3 ^ j := by
      apply div_lt_div_of_pos_right _ hpos; linarith
    linarith
  · have : ((z i : ℝ) + 1 / 2) / 3 ^ j < ((z i : ℝ) + 1) / 3 ^ j := by
      apply div_lt_div_of_pos_right _ hpos; linarith
    linarith

theorem volume_box (j : ℕ) (z : Fin d → ℕ) :
    volume (box j z) = ENNReal.ofReal (((3 : ℝ) ^ j)⁻¹) ^ d := by
  have hpos : (0 : ℝ) < 3 ^ j := by positivity
  have : box j z = Set.pi Set.univ (fun i => Set.Ioo ((z i : ℝ) / 3 ^ j - 1 / 2)
      (((z i : ℝ) + 1) / 3 ^ j - 1 / 2)) := by
    ext x; simp [box]
  rw [this, volume_pi_pi]
  simp only [Real.volume_Ioo]
  have hh : ∀ i : Fin d, ((((z i : ℝ) + 1) / 3 ^ j - 1 / 2) - ((z i : ℝ) / 3 ^ j - 1 / 2)) =
      ((3 : ℝ) ^ j)⁻¹ := fun i => by field_simp; ring
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Real volume of a cube. -/
theorem volume_box_toReal (j : ℕ) (z : Fin d → ℕ) :
    (volume (box j z)).toReal = (((3 : ℝ) ^ j)⁻¹) ^ d := by
  rw [volume_box, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

/-- Nested boxes: sharing a point forces containment of the finer one. -/
theorem box_subset_of_mem {i j : ℕ} (hij : i ≤ j) {w z : Fin d → ℕ} {x : Vec d}
    (hw : x ∈ box i w) (hz : x ∈ box j z) : box j z ⊆ box i w := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
  intro y hy a
  have hp1 : (0 : ℝ) < 3 ^ i := by positivity
  have hpm : (0 : ℝ) < 3 ^ m := by positivity
  have h3 : (3 : ℝ) ^ (i + m) = 3 ^ i * 3 ^ m := pow_add _ _ _
  have hwa := hw a
  have hza := hz a
  have hya := hy a
  -- multiply out
  have e1 : (w a : ℝ) < 3 ^ i * (x a + 1 / 2) ∧ 3 ^ i * (x a + 1 / 2) < w a + 1 := by
    constructor
    · have := (div_lt_iff₀ hp1).mp (by linarith [hwa.1] : (w a : ℝ) / 3 ^ i < x a + 1 / 2)
      linarith
    · have := (lt_div_iff₀ hp1).mp (by linarith [hwa.2] : x a + 1 / 2 < ((w a : ℝ) + 1) / 3 ^ i)
      linarith
  have e2 : (z a : ℝ) < 3 ^ (i + m) * (x a + 1 / 2) ∧ 3 ^ (i + m) * (x a + 1 / 2) < z a + 1 := by
    have hp : (0 : ℝ) < 3 ^ (i + m) := by positivity
    constructor
    · have := (div_lt_iff₀ hp).mp (by linarith [hza.1] : (z a : ℝ) / 3 ^ (i + m) < x a + 1 / 2)
      linarith
    · have := (lt_div_iff₀ hp).mp (by linarith [hza.2] : x a + 1 / 2 < ((z a : ℝ) + 1) / 3 ^ (i + m))
      linarith
  have e3 : (3 : ℝ) ^ (i + m) * (x a + 1 / 2) = 3 ^ m * (3 ^ i * (x a + 1 / 2)) := by
    rw [h3]; ring
  -- integer inequalities: z ≥ w 3^m and z + 1 ≤ (w+1) 3^m
  have hm : (w a : ℝ) * 3 ^ m ≤ z a := by
    have : (w a : ℝ) * 3 ^ m < z a + 1 := by
      calc (w a : ℝ) * 3 ^ m = 3 ^ m * w a := by ring
        _ < 3 ^ m * (3 ^ i * (x a + 1 / 2)) := mul_lt_mul_of_pos_left e1.1 hpm
        _ < z a + 1 := by rw [← e3]; exact e2.2
    have h' : (w a * 3 ^ m : ℕ) < z a + 1 := by exact_mod_cast this
    have : (w a * 3 ^ m : ℕ) ≤ z a := by omega
    exact_mod_cast this
  have hm' : (z a : ℝ) + 1 ≤ ((w a : ℝ) + 1) * 3 ^ m := by
    have : (z a : ℝ) < ((w a : ℝ) + 1) * 3 ^ m := by
      calc (z a : ℝ) < 3 ^ (i + m) * (x a + 1 / 2) := e2.1
        _ = 3 ^ m * (3 ^ i * (x a + 1 / 2)) := e3
        _ < 3 ^ m * (w a + 1) := mul_lt_mul_of_pos_left e1.2 hpm
        _ = _ := by ring
    have h' : (z a : ℕ) < (w a + 1) * 3 ^ m := by exact_mod_cast this
    have : (z a + 1 : ℕ) ≤ (w a + 1) * 3 ^ m := by omega
    exact_mod_cast this
  have hp : (0 : ℝ) < 3 ^ (i + m) := by positivity
  rw [h3] at hya
  constructor
  · have : (w a : ℝ) / 3 ^ i ≤ (z a : ℝ) / (3 ^ i * 3 ^ m) := by
      rw [div_le_div_iff₀ hp1 (by positivity)]
      nlinarith [hm]
    linarith [hya.1]
  · have : ((z a : ℝ) + 1) / (3 ^ i * 3 ^ m) ≤ ((w a : ℝ) + 1) / 3 ^ i := by
      rw [div_le_div_iff₀ (by positivity) hp1]
      nlinarith [hm']
    linarith [hya.2]

/-- Two boxes of the same level sharing a point have the same index. -/
theorem eq_of_mem_box {j : ℕ} {z z' : Fin d → ℕ} {x : Vec d}
    (hz : x ∈ box j z) (hz' : x ∈ box j z') : z = z' := by
  funext a
  have hp : (0 : ℝ) < 3 ^ j := by positivity
  have h1 := hz a; have h2 := hz' a
  have l1 : (z a : ℝ) < 3 ^ j * (x a + 1 / 2) ∧ 3 ^ j * (x a + 1 / 2) < z a + 1 := by
    constructor
    · have := (div_lt_iff₀ hp).mp (by linarith [h1.1] : (z a : ℝ) / 3 ^ j < x a + 1 / 2); linarith
    · have := (lt_div_iff₀ hp).mp (by linarith [h1.2] : x a + 1 / 2 < ((z a : ℝ) + 1) / 3 ^ j); linarith
  have l2 : (z' a : ℝ) < 3 ^ j * (x a + 1 / 2) ∧ 3 ^ j * (x a + 1 / 2) < z' a + 1 := by
    constructor
    · have := (div_lt_iff₀ hp).mp (by linarith [h2.1] : (z' a : ℝ) / 3 ^ j < x a + 1 / 2); linarith
    · have := (lt_div_iff₀ hp).mp (by linarith [h2.2] : x a + 1 / 2 < ((z' a : ℝ) + 1) / 3 ^ j); linarith
  have a1 : (z a : ℝ) < z' a + 1 := by linarith [l1.1, l2.2]
  have a2 : (z' a : ℝ) < z a + 1 := by linarith [l2.1, l1.2]
  have b1 : z a < z' a + 1 := by exact_mod_cast a1
  have b2 : z' a < z a + 1 := by exact_mod_cast a2
  omega

end CoarseDeGiorgi.Cubical
