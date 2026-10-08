import CoarseDeGiorgi.Endpoint.Chaining.Restriction
import CoarseDeGiorgi.Endpoint.Chaining.Norms
import CoarseDeGiorgi.Endpoint.Chaining.Algebra

/-! The interior weak Harnack estimate from fixed-scale rescaled cube estimates. -/
namespace CoarseDeGiorgi.Endpoint
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- The dimensional volume loss in comparison through the smaller overlap cube. -/
noncomputable def chainingOverlapFactor (d : ℕ) (b : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ((1 / 162 : ℝ) ^ d)) ^ (-1 / b) *
    (ENNReal.ofReal ((5 / 216 : ℝ) ^ d)) ^ (1 / b)

theorem chainingOverlapFactor_ne_top (d : ℕ) (b : ℝ) :
    chainingOverlapFactor d b ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_ne_zero (by positivity) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_ne_top_of_ne_zero (by positivity) ENNReal.ofReal_ne_top

theorem weak_grid_step {d N : ℕ} (u : Vec d → ℝ) {b : ℝ} (hb : 0 < b) (A : ℝ≥0∞)
    (hlocal : ∀ m : Fin d → Fin (2 * N + 1),
      normalizedLpMoment b hb (gridCube d (chainingCenter N m) (5 / 8)) u ≤
        A * nonnegativeEssInf (gridCube d (chainingCenter N m) (1 / 2)) u)
    (m n : Fin d → Fin (2 * N + 1))
    (h : ∀ i, |chainingCenter N m i - chainingCenter N n i| ≤ 1 / 81) :
    nonnegativeEssInf (gridCube d (chainingCenter N n) (1 / 2)) u ≤
      (chainingOverlapFactor d b * A) *
        nonnegativeEssInf (gridCube d (chainingCenter N m) (1 / 2)) u := by
  let E := gridCube d (fun i => (chainingCenter N m i + chainingCenter N n i) / 2) (1 / 6)
  let V := gridCube d (chainingCenter N m) (5 / 8)
  have he := overlap_cube_subset _ _ h
  have hEV : E ⊆ V := fun x hx =>
    gridCube_mono _ (by norm_num : (1 / 2 : ℝ) ≤ 5 / 8) (he hx).1
  have hEW : E ⊆ gridCube d (chainingCenter N n) (1 / 2) := fun _ hx => (he hx).2
  have hEvol : volume E = ENNReal.ofReal ((1 / 162 : ℝ) ^ d) := by
    dsimp only [E]
    rw [gridCube_volume _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    norm_num
  have hVvol : volume V = ENNReal.ofReal ((5 / 216 : ℝ) ^ d) := by
    dsimp only [V]
    rw [gridCube_volume _ (by norm_num : (0 : ℝ) ≤ 5 / 8)]
    norm_num
  have hbound := inf_le_moment_of_overlap E V
    (gridCube d (chainingCenter N n) (1 / 2)) u hb hEV hEW
    (by rw [hEvol]; positivity) (by rw [hEvol]; exact ENNReal.ofReal_ne_top)
    (by rw [hVvol]; positivity) (by rw [hVvol]; exact ENNReal.ofReal_ne_top)
  rw [hEvol, hVvol] at hbound
  calc
    _ ≤ chainingOverlapFactor d b * normalizedLpMoment b hb V u := hbound
    _ ≤ chainingOverlapFactor d b * (A *
        nonnegativeEssInf (gridCube d (chainingCenter N m) (1 / 2)) u) :=
      mul_le_mul_of_nonneg_left (hlocal m) zero_le
    _ = _ := (mul_assoc _ _ _).symm

/-- Summation of the local weak estimates after chaining to an infimum seed. -/
theorem weak_grid_chain {d N : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ)
    {b : ℝ} (hb : 0 < b) (A : ℝ≥0∞)
    (hcover : V ⊆ ⋃ m : Fin d → Fin (2 * N + 1), gridCube d (chainingCenter N m) (1 / 2))
    (hlocal : ∀ m : Fin d → Fin (2 * N + 1),
      normalizedLpMoment b hb (gridCube d (chainingCenter N m) (5 / 8)) u ≤
        A * nonnegativeEssInf (gridCube d (chainingCenter N m) (1 / 2)) u) :
    eLpNorm' u b (volume.restrict V) ≤
      ((Fintype.card (Fin d → Fin (2 * N + 1)) : ℝ≥0∞) ^ (1 / b) *
        ENNReal.ofReal ((5 / 216 : ℝ) ^ d) ^ (1 / b) *
          chainingOverlapFactor d b ^ (2 * N)) * A ^ (2 * N + 1) * nonnegativeEssInf V u := by
  let Q : (Fin d → Fin (2 * N + 1)) → Set (Vec d) :=
    fun m => gridCube d (chainingCenter N m) (1 / 2)
  let I := fun m => nonnegativeEssInf (Q m) u
  obtain ⟨m, hm⟩ := exists_cover_inf_le V Q u hcover
  have hc (n : Fin d → Fin (2 * N + 1)) :
      I n ≤ (chainingOverlapFactor d b * A) ^ (2 * N) * nonnegativeEssInf V u :=
    (chaining_inf_le I (chainingOverlapFactor d b * A)
      (weak_grid_step u hb A hlocal) m n).trans (mul_le_mul_of_nonneg_left hm zero_le)
  let M := ENNReal.ofReal ((5 / 216 : ℝ) ^ d) ^ (1 / b) * A *
    ((chainingOverlapFactor d b * A) ^ (2 * N) * nonnegativeEssInf V u)
  have hlocal' (n : Fin d → Fin (2 * N + 1)) :
      eLpNorm' u b (volume.restrict (gridCube d (chainingCenter N n) (5 / 8))) ≤ M := by
    have hvol : volume (gridCube d (chainingCenter N n) (5 / 8)) =
        ENNReal.ofReal ((5 / 216 : ℝ) ^ d) := by
      rw [gridCube_volume _ (by norm_num : (0 : ℝ) ≤ 5 / 8)]
      norm_num
    rw [eLpNorm'_eq_volume_mul_moment _ u hb (by rw [hvol]; positivity)
      (by rw [hvol]; exact ENNReal.ofReal_ne_top), hvol]
    calc
      _ ≤ ENNReal.ofReal ((5 / 216 : ℝ) ^ d) ^ (1 / b) * (A * I n) :=
        mul_le_mul_of_nonneg_left (hlocal n) zero_le
      _ ≤ M := by
        dsimp only [M]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (hc n) zero_le
  have hcover' : V ⊆ ⋃ n : Fin d → Fin (2 * N + 1),
      gridCube d (chainingCenter N n) (5 / 8) := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨n, gridCube_mono _ (by norm_num : (1 / 2 : ℝ) ≤ 5 / 8) hn⟩
  have h := eLpNorm'_cover_le V _ u hb hcover' M hlocal'
  calc
    _ ≤ (Fintype.card (Fin d → Fin (2 * N + 1)) : ℝ≥0∞) ^ (1 / b) * M := h
    _ = _ := by dsimp only [M]; rw [mul_pow, pow_succ]; ac_rfl

/-- The fixed prefactor after the weak Harnack path of length 76. -/
noncomputable def interiorWeakPrefactor (d : ℕ) (b : ℝ) : ℝ≥0∞ :=
  (Fintype.card (Fin d → Fin 77) : ℝ≥0∞) ^ (1 / b) *
    ENNReal.ofReal ((5 / 216 : ℝ) ^ d) ^ (1 / b) * chainingOverlapFactor d b ^ 76

theorem interiorWeakPrefactor_ne_top (d : ℕ) {b : ℝ} (hb : 0 < b) :
    interiorWeakPrefactor d b ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _)
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · exact ENNReal.pow_ne_top (chainingOverlapFactor_ne_top d b)

/-- Chaining and volume conversion prove the exact conclusion of `e.interior.weak.harnack`. -/
theorem interior_weak_harnack_of_cubes (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (hcubes : LocalWeakHarnackCubes d p q s t hp hq hs ht) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          eLpNorm u (ENNReal.ofReal (harnackEtaParam q))
              (volume.restrict (originCube (15 / 16))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (15 / 16)) u := by
  have hb : 0 < harnackEtaParam q := by
    have hq0 : 0 < q := zero_lt_one.trans hq
    dsimp [harnackEtaParam, paramR]
    positivity
  obtain ⟨C, hC, hlocal⟩ := hcubes
  let K := interiorWeakPrefactor d (harnackEtaParam q)
  refine ⟨K.toReal + 77 * C, add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (by norm_num) hC), ?_⟩
  intro a ha hU hL u G hu0 hu
  let : NeZero d := ⟨by omega⟩
  let A := ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal))
  have hsub (m : Fin d → Fin 77) : gridCube d (chainingCenter 38 m) 1 ⊆ originCube 1 :=
    chainingCube_subset (N := 38) m (by norm_num)
  have hloc (m : Fin d → Fin 77) :
      normalizedLpMoment (harnackEtaParam q) hb (gridCube d (chainingCenter 38 m) (5 / 8)) u ≤
        A * nonnegativeEssInf (gridCube d (chainingCenter 38 m) (1 / 2)) u := by
    apply hlocal a ha hU hL (chainingCenter 38 m) (chainingCenter_grid (N := 38) m) (hsub m) u G
    · exact ae_restrict_of_ae_restrict_of_subset (hsub m) hu0
    · exact weighted_supersolution_restrict (originCube_domain one_pos)
        (originCube_nonempty one_pos) ha (gridCube_domain _ one_pos) (hsub m) hu
  have hcover : originCube (d := d) (15 / 16) ⊆ ⋃ m : Fin d → Fin 77,
      gridCube d (chainingCenter 38 m) (1 / 2) := chaining_halves_cover (N := 38) (by norm_num)
  have hbound : eLpNorm' u (harnackEtaParam q) (volume.restrict (originCube (15 / 16))) ≤
      K * A ^ 77 * nonnegativeEssInf (originCube (15 / 16)) u :=
    weak_grid_chain (N := 38) (originCube (15 / 16)) u hb A hcover hloc
  have hmeas : AEStronglyMeasurable u (volume.restrict (originCube 1)) := by
    simpa only [Pi.neg_def, neg_neg] using hu.1.1.neg
  have hmeas' := hmeas.mono_set
    (originCube_mono' (by norm_num : (0 : ℝ) < 15 / 16) one_pos (by norm_num))
  have hnorm := eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hb).ne'
    ENNReal.ofReal_ne_top hmeas'
  rw [ENNReal.toReal_ofReal hb.le] at hnorm
  rw [← hnorm] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (chaining_absorb K (interiorWeakPrefactor_ne_top d hb) C _
      (chaining_sqrt_contrast_ge_one (by omega) a ha hp.le hq.le hs ht hU hL) 77) zero_le)

end CoarseDeGiorgi.Endpoint
