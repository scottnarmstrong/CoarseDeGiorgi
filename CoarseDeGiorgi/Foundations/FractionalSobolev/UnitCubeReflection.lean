import CoarseDeGiorgi.Foundations.FractionalSobolev.Sobolev
import CoarseDeGiorgi.Statements.DnpvUnitCube
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

/-- The coordinate fold on the three reflected copies of the unit interval. -/
def cubeFoldCoord (t : ℝ) : ℝ := max (min t (1 - t)) (-1 - t)
def cubeFold {n : ℕ} (x : Vec n) : Vec n := fun i => cubeFoldCoord (x i)
def reflectedCube (n : ℕ) : Set (Vec n) := {x | ∀ i, (-3 / 2 : ℝ) < x i ∧ x i < 3 / 2}

def cubeReflectCoord (q : Fin 3) (t : ℝ) : ℝ :=
  if q = 0 then -1 - t else if q = 1 then t else 1 - t
def cubeReflect {n : ℕ} (q : Fin n → Fin 3) (x : Vec n) : Vec n :=
  fun i => cubeReflectCoord (q i) (x i)
def cubeReflectionCell {n : ℕ} (q : Fin n → Fin 3) : Set (Vec n) :=
  cubeReflect q ⁻¹' dnpvUnitCube n

lemma cubeReflectCoord_involutive (q : Fin 3) : Function.Involutive (cubeReflectCoord q) := by
  intro t
  fin_cases q <;> norm_num [cubeReflectCoord]

lemma cubeReflect_involutive {n : ℕ} (q : Fin n → Fin 3) : Function.Involutive (cubeReflect q) := by
  intro x
  funext i
  exact cubeReflectCoord_involutive (q i) (x i)

lemma cubeReflect_continuous {n : ℕ} (q : Fin n → Fin 3) : Continuous (cubeReflect q) := by
  apply continuous_pi
  intro i
  unfold cubeReflect cubeReflectCoord
  split_ifs <;> fun_prop

def cubeReflectHomeomorph {n : ℕ} (q : Fin n → Fin 3) : Vec n ≃ₜ Vec n where
  toFun := cubeReflect q
  invFun := cubeReflect q
  left_inv := cubeReflect_involutive q
  right_inv := cubeReflect_involutive q
  continuous_toFun := cubeReflect_continuous q
  continuous_invFun := cubeReflect_continuous q

lemma cubeReflect_preserving {n : ℕ} (q : Fin n → Fin 3) : MeasurePreserving (cubeReflect q) := by
  have hneg : MeasurePreserving (Neg.neg : ℝ → ℝ) (volume : Measure ℝ) volume := by
    refine ⟨measurable_neg, ?_⟩
    simpa using (Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0))
  have hm (c : ℝ) : MeasurePreserving (fun t : ℝ => c - t) (volume : Measure ℝ) volume := by
    convert (measurePreserving_add_right (volume : Measure ℝ) c).comp hneg using 1
    funext t
    simp only [Function.comp_apply]
    ring
  change MeasurePreserving (fun x : Vec n => fun i => cubeReflectCoord (q i) (x i))
  apply volume_preserving_pi
  intro i
  generalize hqi : q i = j
  fin_cases j
  · convert hm (-1) using 1
    funext t
    norm_num [cubeReflectCoord]
  · convert (show MeasurePreserving (id : ℝ → ℝ) (volume : Measure ℝ) volume from ⟨measurable_id, Measure.map_id⟩) using 1
    funext t
    norm_num [cubeReflectCoord]
  · convert hm 1 using 1
    funext t
    norm_num [cubeReflectCoord]

lemma unitCube_open (n : ℕ) : IsOpen (dnpvUnitCube n) := by
  have heq : dnpvUnitCube n = ⋂ i : Fin n, {x : Vec n | (-1 / 2 : ℝ) < x i ∧ x i < 1 / 2} := by
    ext x; simp only [dnpvUnitCube, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioo.preimage (continuous_apply i)

lemma reflectedCube_open (n : ℕ) : IsOpen (reflectedCube n) := by
  have heq : reflectedCube n = ⋂ i : Fin n, {x : Vec n | (-3 / 2 : ℝ) < x i ∧ x i < 3 / 2} := by
    ext x; simp only [reflectedCube, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioo.preimage (continuous_apply i)

lemma cubeReflectionCell_measurable {n : ℕ} (q : Fin n → Fin 3) :
    MeasurableSet (cubeReflectionCell q) :=
  (unitCube_open n).measurableSet.preimage (cubeReflect_continuous q).measurable

lemma cubeFoldCoord_eq_reflect (q : Fin 3) {t : ℝ}
    (ht : (-1 / 2 : ℝ) < cubeReflectCoord q t ∧ cubeReflectCoord q t < 1 / 2) :
    cubeFoldCoord t = cubeReflectCoord q t := by
  fin_cases q <;> norm_num [cubeReflectCoord] at ht ⊢
  · unfold cubeFoldCoord
    rw [min_eq_left (by linarith [ht.1, ht.2]), max_eq_right (by linarith [ht.1, ht.2])]
  · unfold cubeFoldCoord
    rw [min_eq_left (by linarith [ht.1, ht.2]), max_eq_left (by linarith [ht.1, ht.2])]
  · unfold cubeFoldCoord
    rw [min_eq_right (by linarith [ht.1, ht.2]), max_eq_left (by linarith [ht.1, ht.2])]

lemma cubeFold_eq_reflect {n : ℕ} (q : Fin n → Fin 3) {x : Vec n}
    (hx : x ∈ cubeReflectionCell q) : cubeFold x = cubeReflect q x := by
  funext i
  exact cubeFoldCoord_eq_reflect (q i) (hx i)

lemma cubeFold_eq_self {n : ℕ} {x : Vec n} (hx : x ∈ dnpvUnitCube n) : cubeFold x = x := by
  funext i
  change cubeFoldCoord (x i) = x i
  simpa only [cubeReflectCoord, show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true] using
    cubeFoldCoord_eq_reflect 1 (by simpa [cubeReflectCoord] using hx i)

lemma cubeFoldCoord_lipschitz : LipschitzWith 1 cubeFoldCoord := by
  have hm (c : ℝ) : LipschitzWith 1 (fun t : ℝ => c - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
      show c - x - (c - y) = -(x - y) by ring, abs_neg]
  change LipschitzWith 1 (fun t : ℝ => max (min t (1 - t)) (-1 - t))
  simpa only [max_self, id_eq] using (LipschitzWith.id.min (hm 1)).max (hm (-1))

lemma cubeFold_continuous {n : ℕ} : Continuous (cubeFold (n := n)) :=
  continuous_pi (fun i => cubeFoldCoord_lipschitz.continuous.comp (continuous_apply i))

lemma cubeFold_distance_le {n : ℕ} (x y : Vec n) : euclidDist (cubeFold x) (cubeFold y) ≤ euclidDist x y := by
  unfold euclidDist
  apply Real.sqrt_le_sqrt
  unfold vecNormSq vecDot
  apply Finset.sum_le_sum
  intro i _
  have hi := cubeFoldCoord_lipschitz.dist_le_mul (x i) (y i)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hi
  change (cubeFoldCoord (x i) - cubeFoldCoord (y i)) *
      (cubeFoldCoord (x i) - cubeFoldCoord (y i)) ≤ (x i - y i) * (x i - y i)
  nlinarith only [sq_abs (cubeFoldCoord (x i) - cubeFoldCoord (y i)), sq_abs (x i - y i),
    mul_self_le_mul_self (abs_nonneg _) hi]

lemma reflectedCube_covered_ae (n : ℕ) :
    reflectedCube n =ᵐ[volume] ⋃ q : Fin n → Fin 3, cubeReflectionCell q := by
  have hfaces : ∀ᵐ x : Vec n ∂volume, ∀ i, x i ≠ (-1 / 2 : ℝ) ∧ x i ≠ (1 / 2 : ℝ) := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) i (-1 / 2)).and
      (Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) i (1 / 2))
  filter_upwards [hfaces] with x hx
  apply propext
  constructor
  · intro hV
    let q : Fin n → Fin 3 := fun i => if x i < -1 / 2 then 0 else if x i < 1 / 2 then 1 else 2
    apply Set.mem_iUnion.mpr
    refine ⟨q, fun i => ?_⟩
    change (-1 / 2 : ℝ) < cubeReflectCoord (q i) (x i) ∧ cubeReflectCoord (q i) (x i) < 1 / 2
    by_cases hl : x i < -1 / 2
    · dsimp [q]
      rw [ite_eq_left hl]
      norm_num [cubeReflectCoord]
      constructor <;> linarith [(hV i).1, (hV i).2]
    · by_cases hr : x i < 1 / 2
      · dsimp [q]
        rw [ite_eq_right hl, ite_eq_left hr]
        norm_num [cubeReflectCoord]
        have hlow : (-1 / 2 : ℝ) < x i := lt_of_le_of_ne (le_of_not_gt hl) (hx i).1.symm
        exact ⟨by linarith, hr⟩
      · dsimp [q]
        rw [ite_eq_right hl, ite_eq_right hr]
        norm_num [cubeReflectCoord]
        have hr' := lt_of_le_of_ne (le_of_not_gt hr) (hx i).2.symm
        constructor <;> linarith [(hV i).1, (hV i).2]
  · intro hu
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hu
    intro i
    have ht := hq i
    change (-1 / 2 : ℝ) < cubeReflectCoord (q i) (x i) ∧ cubeReflectCoord (q i) (x i) < 1 / 2 at ht
    generalize hqi : q i = j at ht
    fin_cases j <;> norm_num [cubeReflectCoord] at ht <;>
      constructor <;> linarith [ht.1, ht.2]

/-- Each reflected copy carries exactly one copy of the original Lebesgue integral. -/
lemma cubeReflectionCell_lintegral {n : ℕ} (q : Fin n → Fin 3) (h : Vec n → ℝ≥0∞) :
    (∫⁻ x in cubeReflectionCell q, h (cubeFold x)) = ∫⁻ x in dnpvUnitCube n, h x := by
  calc
    _ = ∫⁻ x in cubeReflectionCell q, h (cubeReflect q x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (cubeReflectionCell_measurable q)] with x hx
      rw [cubeFold_eq_reflect q hx]
    _ = _ := ((cubeReflect_preserving q).restrict_preimage_emb
      (cubeReflectHomeomorph q).measurableEmbedding (dnpvUnitCube n)).lintegral_comp_emb
        (cubeReflectHomeomorph q).measurableEmbedding h

/-- The fold has multiplicity at most 3^n; boundary hyperplanes are null. -/
lemma cubeFold_lintegral_le {n : ℕ} (h : Vec n → ℝ≥0∞) :
    (∫⁻ x in reflectedCube n, h (cubeFold x)) ≤
      (3 ^ n : ℝ≥0∞) * ∫⁻ x in dnpvUnitCube n, h x := by
  rw [Measure.restrict_congr_set (reflectedCube_covered_ae n)]
  calc
    _ ≤ ∑' q : Fin n → Fin 3, ∫⁻ x in cubeReflectionCell q, h (cubeFold x) := lintegral_iUnion_le _ _
    _ = _ := by
      simp only [cubeReflectionCell_lintegral, tsum_fintype, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
