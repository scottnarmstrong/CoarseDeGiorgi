import CoarseDeGiorgi.Endpoint.CubeInterface
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! Fixed grid boxes and overlaps for the interior estimates. -/
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi.Endpoint
noncomputable section

/-- The centres of a finite coordinate box in the `1/81` grid. -/
def chainingCenter {d : ℕ} (N : ℕ) (m : Fin d → Fin (2 * N + 1)) : Vec d :=
  fun i => ((m i : ℕ) - (N : ℝ)) / 81

theorem chainingCenter_grid {d N : ℕ} (m : Fin d → Fin (2 * N + 1)) :
    IsGridPoint d (chainingCenter N m) := by
  intro i
  refine ⟨(m i : ℕ) - (N : ℤ), ?_⟩
  simp only [chainingCenter, Int.cast_sub, Int.cast_natCast]

theorem mem_gridCube_iff {d : ℕ} (x y : Vec d) (ρ : ℝ) :
    x ∈ gridCube d y ρ ↔ ∀ i, |x i - y i| < ρ / 54 := by
  simp only [gridCube, originCube, Set.mem_ofPred_eq, Pi.sub_apply, abs_lt]
  norm_num
  ring_nf

theorem gridCube_eq_pi {d : ℕ} (y : Vec d) (ρ : ℝ) :
    gridCube d y ρ = Set.pi Set.univ
      (fun i => Set.Ioo (y i - ρ / 54) (y i + ρ / 54)) := by
  ext x
  rw [mem_gridCube_iff]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo, abs_lt]
  constructor <;> intro h i <;> constructor <;> linarith [h i]

theorem gridCube_volume {d : ℕ} (y : Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (gridCube d y ρ) = ENNReal.ofReal ((ρ / 27) ^ d) := by
  rw [gridCube_eq_pi, Real.volume_pi_Ioo]
  simp only [show ∀ i, y i + ρ / 54 - (y i - ρ / 54) = ρ / 27 by intro i; ring,
    Finset.prod_const, Finset.card_fin, ENNReal.ofReal_pow (by positivity : 0 ≤ ρ / 27)]

theorem gridCube_mono {d : ℕ} (y : Vec d) {ρ R : ℝ} (h : ρ ≤ R) :
    gridCube d y ρ ⊆ gridCube d y R := by
  intro x hx
  rw [mem_gridCube_iff] at hx ⊢
  intro i
  exact (hx i).trans_le (div_le_div_of_nonneg_right h (by norm_num))

theorem chainingCenter_bound {d N : ℕ} (m : Fin d → Fin (2 * N + 1)) (i : Fin d) :
    |chainingCenter N m i| ≤ N / 81 := by
  have hm : (m i : ℕ) ≤ 2 * N := by omega
  have hm' : (m i : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hm
  have hm0 : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
  rw [chainingCenter, abs_le]
  constructor <;> linarith

theorem chainingCube_subset {d N : ℕ} (m : Fin d → Fin (2 * N + 1))
    {R : ℝ} (hR : (N : ℝ) / 81 + 1 / 54 ≤ R / 2) :
    gridCube d (chainingCenter N m) 1 ⊆ originCube R := by
  intro x hx i
  have hxi := (mem_gridCube_iff x _ 1).mp hx i
  have hmi := chainingCenter_bound m i
  have hxabs : |x i| < R / 2 := calc
    |x i| = |(x i - chainingCenter N m i) + chainingCenter N m i| := by congr 1; ring
    _ ≤ |x i - chainingCenter N m i| + |chainingCenter N m i| := abs_add_le _ _
    _ < 1 / 54 + (N : ℝ) / 81 := add_lt_add_of_lt_of_le hxi hmi
    _ ≤ R / 2 := by linarith
  exact abs_lt.mp hxabs

theorem overlap_cube_subset {d : ℕ} (y z : Vec d)
    (h : ∀ i, |y i - z i| ≤ 1 / 81) :
    gridCube d (fun i => (y i + z i) / 2) (1 / 6) ⊆
      gridCube d y (1 / 2) ∩ gridCube d z (1 / 2) := by
  intro x hx
  rw [mem_gridCube_iff] at hx
  constructor
  · rw [mem_gridCube_iff]
    intro i
    have hmid : |(y i + z i) / 2 - y i| ≤ 1 / 162 := by
      rw [show (y i + z i) / 2 - y i = -(y i - z i) / 2 by ring,
        abs_div, abs_neg]
      norm_num
      linarith [h i]
    calc
      |x i - y i| = |(x i - (y i + z i) / 2) + ((y i + z i) / 2 - y i)| := by
        congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ < (1 / 6 : ℝ) / 54 + 1 / 162 := add_lt_add_of_lt_of_le (hx i) hmid
      _ = (1 / 2 : ℝ) / 54 := by norm_num
  · rw [mem_gridCube_iff]
    intro i
    have hmid : |(y i + z i) / 2 - z i| ≤ 1 / 162 := by
      rw [show (y i + z i) / 2 - z i = (y i - z i) / 2 by ring, abs_div]
      norm_num
      linarith [h i]
    calc
      |x i - z i| = |(x i - (y i + z i) / 2) + ((y i + z i) / 2 - z i)| := by
        congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ < (1 / 6 : ℝ) / 54 + 1 / 162 := add_lt_add_of_lt_of_le (hx i) hmid
      _ = (1 / 2 : ℝ) / 54 := by norm_num

/-- Central halves of the finite grid box cover the indicated centered cube. -/
theorem chaining_halves_cover {d N : ℕ} {R : ℝ}
    (hR : 81 * (R / 2) + 1 / 2 < (N : ℝ) + 1) :
    originCube (d := d) R ⊆ ⋃ m : Fin d → Fin (2 * N + 1),
      gridCube d (chainingCenter N m) (1 / 2) := by
  intro x hx
  have hround (i : Fin d) :
      0 ≤ ⌊81 * x i + (N : ℝ) + 1 / 2⌋ ∧
        ⌊81 * x i + (N : ℝ) + 1 / 2⌋ < (2 * N + 1 : ℕ) := by
    have hx' := hx i
    have hlo : 0 ≤ 81 * x i + (N : ℝ) + 1 / 2 := by
      linarith
    refine ⟨Int.floor_nonneg.mpr hlo, Int.floor_lt.mpr ?_⟩
    push_cast
    linarith
  let m : Fin d → Fin (2 * N + 1) := fun i =>
    ⟨(⌊81 * x i + (N : ℝ) + 1 / 2⌋).toNat, by
      have hi := hround i
      omega⟩
  apply Set.mem_iUnion.mpr
  refine ⟨m, (mem_gridCube_iff x _ _).mpr ?_⟩
  intro i
  have hm : (m i : ℝ) = (⌊81 * x i + (N : ℝ) + 1 / 2⌋ : ℝ) := by
    dsimp [m]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hround i).1]
  have hlo := Int.floor_le (81 * x i + (N : ℝ) + 1 / 2)
  have hhi := Int.lt_floor_add_one (81 * x i + (N : ℝ) + 1 / 2)
  dsimp [chainingCenter]
  rw [hm, abs_lt]
  constructor <;> linarith

/-- A fixed length path that moves every coordinate towards its target. -/
def chainingPath {d N : ℕ} (m n : Fin d → Fin (2 * N + 1)) (k : ℕ) :
    Fin d → Fin (2 * N + 1) := fun i =>
  ⟨if (m i : ℕ) ≤ n i then min (n i : ℕ) ((m i : ℕ) + k)
    else max (n i : ℕ) ((m i : ℕ) - k), by
      have hm := (m i).isLt
      have hn := (n i).isLt
      split_ifs <;> omega⟩

theorem chainingPath_zero {d N : ℕ} (m n : Fin d → Fin (2 * N + 1)) :
    chainingPath m n 0 = m := by
  funext i
  apply Fin.ext
  dsimp [chainingPath]
  split_ifs <;> omega

theorem chainingPath_end {d N : ℕ} (m n : Fin d → Fin (2 * N + 1)) :
    chainingPath m n (2 * N) = n := by
  funext i
  apply Fin.ext
  have hm := (m i).isLt
  have hn := (n i).isLt
  dsimp [chainingPath]
  split_ifs <;> omega

theorem chainingPath_step {d N : ℕ} (m n : Fin d → Fin (2 * N + 1)) (k : ℕ) :
    ∀ i, |chainingCenter N (chainingPath m n k) i -
      chainingCenter N (chainingPath m n (k + 1)) i| ≤ 1 / 81 := by
  intro i
  have hstep :
      (chainingPath m n k i : ℕ) ≤ (chainingPath m n (k + 1) i : ℕ) + 1 ∧
      (chainingPath m n (k + 1) i : ℕ) ≤ (chainingPath m n k i : ℕ) + 1 := by
    dsimp [chainingPath]
    split_ifs <;> omega
  have h1 : (chainingPath m n k i : ℝ) ≤
      (chainingPath m n (k + 1) i : ℝ) + 1 := by exact_mod_cast hstep.1
  have h2 : (chainingPath m n (k + 1) i : ℝ) ≤
      (chainingPath m n k i : ℝ) + 1 := by exact_mod_cast hstep.2
  dsimp [chainingCenter]
  rw [abs_le]
  constructor <;> linarith

end
end CoarseDeGiorgi.Endpoint
