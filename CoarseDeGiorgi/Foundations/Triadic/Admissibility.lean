import CoarseDeGiorgi.Foundations.Triadic.Nesting
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization

noncomputable section

variable {d : ℕ}

def clamp (a t : ℝ) : ℝ := if t < -a then -a else if a < t then a else t

theorem clamp_abs_le {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : |clamp a t| ≤ a := by
  unfold clamp
  split_ifs with h1 h2 <;> rw [abs_le] <;> constructor <;> linarith

theorem clamp_sub_abs_le {a b t : ℝ} (hb : 0 ≤ b)
    (ht : |t| ≤ a + b) : |clamp a t - t| ≤ b := by
  have ht' := abs_le.mp ht
  unfold clamp
  split_ifs with h1 h2 <;> rw [abs_le] <;> constructor <;>
    linarith

theorem admissible_iff (τ : ℝ) (hτ : 0 ≤ τ) (D : TriadicCube d) :
    Admissible τ D ↔ ∃ i, τ / 2 + 5 * cubeScaleFactor D / 2 < |center D i| := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    let y : Vec d := fun i => clamp (τ / 2) (center D i)
    have hyR : y ∈ referenceCube τ := fun i => clamp_abs_le (by linarith) _
    have hyD : y ∈ fivefoldCube D := fun i =>
      clamp_sub_abs_le (by linarith only [scaleFactor_pos D]) (hn i)
    exact Set.disjoint_left.mp h hyD hyR
  · rintro ⟨i, hi⟩
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hh : |center D i| ≤ |x i - center D i| + |x i| := by
      have hab := abs_sub_le (center D i) (x i) 0
      simpa only [sub_zero, abs_sub_comm, add_comm] using hab
    linarith only [hi, hh, hx i, hy i]

theorem scaleFactor_mono {D E : TriadicCube d} (h : D.scale ≤ E.scale) :
    cubeScaleFactor D ≤ cubeScaleFactor E :=
  zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) h

theorem fivefoldCube_subset {D E : TriadicCube d}
    (hscale : D.scale ≤ E.scale) (hsub : closedCube D ⊆ closedCube E) :
    fivefoldCube D ⊆ fivefoldCube E := by
  have hfac := scaleFactor_mono hscale
  intro x hx i
  have hi := (closedCube_subset_iff D E).mp hsub i
  calc
    |x i - center E i| ≤ |x i - center D i| + |center D i - center E i| :=
      abs_sub_le _ _ _
    _ ≤ 5 * cubeScaleFactor E / 2 := by linarith only [hx i, hi, hfac]

theorem Admissible.of_subset {τ : ℝ} {D E : TriadicCube d}
    (hE : Admissible τ E) (hscale : D.scale ≤ E.scale)
    (hsub : closedCube D ⊆ closedCube E) : Admissible τ D :=
  hE.mono_left (fivefoldCube_subset hscale hsub)

theorem exterior_small_cubes_admissible {τ : ℝ} (hτ : 0 ≤ τ) {x : Vec d}
    (hx : x ∉ referenceCube τ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ D : TriadicCube d,
      x ∈ closedCube D → cubeScaleFactor D < ε → Admissible τ D := by
  obtain ⟨i, hi⟩ : ∃ i, τ / 2 < |x i| := by
    change ¬∀ i, |x i| ≤ τ / 2 at hx
    push Not at hx
    exact hx
  refine ⟨(|x i| - τ / 2) / 3, by linarith only [hi], ?_⟩
  intro D hxD hsize
  apply (admissible_iff τ hτ D).mpr
  refine ⟨i, ?_⟩
  have hh : |x i| ≤ |x i - center D i| + |center D i| := by
    simpa only [sub_zero] using abs_sub_le (x i) (center D i) 0
  linarith only [hh, hxD i, hsize]

theorem large_cube_not_admissible {τ : ℝ} (hτ : 0 ≤ τ) {x : Vec d}
    (D : TriadicCube d) (hx : x ∈ closedCube D)
    (hsize : ‖x‖ + 1 < cubeScaleFactor D) : ¬Admissible τ D := by
  have hzeroR : (0 : Vec d) ∈ referenceCube τ := by
    intro i
    simpa only [Pi.zero_apply, abs_zero] using (by linarith : (0 : ℝ) ≤ τ / 2)
  have hzeroD : (0 : Vec d) ∈ fivefoldCube D := by
    intro i
    have hnorm : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hh : |center D i| ≤ |x i - center D i| + |x i| := by
      simpa only [sub_zero, abs_sub_comm, add_comm] using abs_sub_le (center D i) (x i) 0
    change |0 - center D i| ≤ 5 * cubeScaleFactor D / 2
    rw [zero_sub, abs_neg]
    linarith only [hx i, hh, hnorm, hsize, norm_nonneg x]
  intro h
  exact Set.disjoint_left.mp h hzeroD hzeroR

theorem exists_closedCube_at_scale (x : Vec d) (k : ℤ) :
    ∃ D : TriadicCube d, D.scale = k ∧ x ∈ closedCube D := by
  let a : ℝ := (3 : ℝ) ^ k
  have ha : 0 < a := by dsimp [a]; positivity
  let D : TriadicCube d := ⟨k, fun i => ⌊x i / a + 1 / 2⌋⟩
  refine ⟨D, rfl, ?_⟩
  intro i
  have hl := Int.floor_le (x i / a + 1 / 2)
  have hu := Int.lt_floor_add_one (x i / a + 1 / 2)
  have hmul := div_mul_cancel₀ (x i) (ne_of_gt ha)
  change |x i - (⌊x i / a + 1 / 2⌋ : ℝ) * a| ≤ a / 2
  rw [abs_le]
  constructor <;> nlinarith only [hl, hu, hmul, ha]

theorem exists_arbitrarily_small_closedCube (x : Vec d) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : TriadicCube d, x ∈ closedCube D ∧ cubeScaleFactor D < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨D, hs, hx⟩ := exists_closedCube_at_scale x (-(n : ℤ))
  refine ⟨D, hx, ?_⟩
  simpa only [cubeScaleFactor, hs, zpow_neg, zpow_natCast, one_div, inv_pow] using hn

theorem exists_arbitrarily_small_admissible {τ : ℝ} (hτ : 0 ≤ τ) {x : Vec d}
    (hx : x ∉ referenceCube τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : TriadicCube d, x ∈ closedCube D ∧ cubeScaleFactor D < ε ∧ Admissible τ D := by
  obtain ⟨δ, hδ, hsmall⟩ := exterior_small_cubes_admissible hτ hx
  obtain ⟨D, hxD, hsize⟩ := exists_arbitrarily_small_closedCube x (lt_min hε hδ)
  exact ⟨D, hxD, hsize.trans_le (min_le_left _ _), hsmall D hxD
    (hsize.trans_le (min_le_right _ _))⟩

end

end CoarseDeGiorgi.Foundations.Triadic
