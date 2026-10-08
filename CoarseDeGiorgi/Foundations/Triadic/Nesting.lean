import CoarseDeGiorgi.Foundations.Triadic.Basic

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization

noncomputable section

variable {d : ℕ}

/-- Ported from the one-dimensional argument in HCP's `StandardCell.lean`. -/
theorem interval_bounds_of_overlap {a : ℝ} (ha : 0 < a) (n : ℕ)
    {w w' : ℤ} {x : ℝ}
    (h1 : ((w : ℝ) - 1 / 2) * a < x)
    (h2 : x < ((w : ℝ) + 1 / 2) * a)
    (h3 : ((w' : ℝ) - 1 / 2) * ((3 : ℝ) ^ n * a) < x)
    (h4 : x < ((w' : ℝ) + 1 / 2) * ((3 : ℝ) ^ n * a)) :
    ((w' : ℝ) - 1 / 2) * ((3 : ℝ) ^ n * a) ≤ ((w : ℝ) - 1 / 2) * a ∧
      ((w : ℝ) + 1 / 2) * a ≤ ((w' : ℝ) + 1 / 2) * ((3 : ℝ) ^ n * a) := by
  obtain ⟨m, hm⟩ : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
  have hm' : (3 : ℝ) ^ n = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  rw [hm'] at h3 h4 ⊢
  have hA : ((w : ℝ) - 1 / 2) < ((w' : ℝ) + 1 / 2) * (2 * (m : ℝ) + 1) := by
    nlinarith only [ha, h1.trans h4]
  have hB : ((w' : ℝ) - 1 / 2) * (2 * (m : ℝ) + 1) < ((w : ℝ) + 1 / 2) := by
    nlinarith only [ha, h3.trans h2]
  have hA' : w - (2 * m + 1) * w' ≤ m := by
    have hh : (w : ℝ) - (2 * (m : ℝ) + 1) * w' < (m : ℝ) + 1 := by linarith only [hA]
    have hh' : w - (2 * m + 1) * w' < m + 1 := by exact_mod_cast hh
    omega
  have hB' : (2 * m + 1) * w' - w ≤ m := by
    have hh : (2 * (m : ℝ) + 1) * w' - (w : ℝ) < (m : ℝ) + 1 := by linarith only [hB]
    have hh' : (2 * m + 1) * w' - w < m + 1 := by exact_mod_cast hh
    omega
  have hA'' : ((w : ℝ) - (2 * (m : ℝ) + 1) * w') ≤ m := by exact_mod_cast hA'
  have hB'' : ((2 * (m : ℝ) + 1) * w' - (w : ℝ)) ≤ m := by exact_mod_cast hB'
  constructor <;> nlinarith only [ha, hA'', hB'']

theorem closedCube_subset_or_openCubeSet_disjoint (D E : TriadicCube d)
    (hscale : D.scale ≤ E.scale) :
    closedCube D ⊆ closedCube E ∨
      Disjoint (Homogenization.openCubeSet D) (Homogenization.openCubeSet E) := by
  by_cases hdis : Disjoint (Homogenization.openCubeSet D) (Homogenization.openCubeSet E)
  · exact Or.inr hdis
  left
  obtain ⟨x, hx, hx'⟩ := Set.not_disjoint_iff.mp hdis
  have hpow : cubeScaleFactor E = (3 : ℝ) ^ ((E.scale - D.scale).toNat) * cubeScaleFactor D := by
    unfold cubeScaleFactor
    rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hscale),
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  intro y hy i
  obtain ⟨hL, hR⟩ := interval_bounds_of_overlap (scaleFactor_pos D)
    ((E.scale - D.scale).toNat) (hx i).1 (hx i).2
      (by simpa only [hpow] using (hx' i).1)
      (by simpa only [hpow] using (hx' i).2)
  rw [← hpow] at hL hR
  have hyi := abs_le.mp (hy i)
  change |y i - (E.index i : ℝ) * cubeScaleFactor E| ≤ cubeScaleFactor E / 2
  rw [abs_le]
  dsimp [center] at hyi
  constructor <;> linarith only [hL, hR, hyi.1, hyi.2]

theorem eq_of_scale_eq_of_overlap (D E : TriadicCube d)
    (hscale : D.scale = E.scale) {x : Vec d}
    (hx : x ∈ Homogenization.openCubeSet D)
    (hx' : x ∈ Homogenization.openCubeSet E) : D = E := by
  have hfac : cubeScaleFactor E = cubeScaleFactor D := by simp only [cubeScaleFactor, hscale]
  have hind : D.index = E.index := by
    funext i
    have hi := hx i
    have hi' := hx' i
    rw [hfac] at hi'
    have h1 : (D.index i : ℝ) < (E.index i : ℝ) + 1 := by
      nlinarith only [hi.1, hi'.2, scaleFactor_pos D]
    have h2 : (E.index i : ℝ) < (D.index i : ℝ) + 1 := by
      nlinarith only [hi'.1, hi.2, scaleFactor_pos D]
    have h1' : D.index i < E.index i + 1 := by exact_mod_cast h1
    have h2' : E.index i < D.index i + 1 := by exact_mod_cast h2
    omega
  cases D
  cases E
  exact congrArg₂ TriadicCube.mk hscale hind

theorem center_mem_openCubeSet_of_subset (D E : TriadicCube d)
    (hsub : closedCube D ⊆ closedCube E) :
    center D ∈ Homogenization.openCubeSet E := by
  intro i
  have hi := (closedCube_subset_iff D E).mp hsub i
  have hh : |center D i - center E i| < cubeScaleFactor E / 2 := by
    linarith only [hi, scaleFactor_pos D]
  obtain ⟨hl, hu⟩ := abs_lt.mp hh
  dsimp [center] at hl hu ⊢
  constructor <;> linarith only [hl, hu]

theorem eq_ancestor_of_scale_of_subset (D E : TriadicCube d) (n : ℕ)
    (hscale : E.scale = D.scale + n) (hsub : closedCube D ⊆ closedCube E) :
    E = ancestor D n := by
  exact eq_of_scale_eq_of_overlap E (ancestor D n)
    (hscale.trans (ancestor_scale D n).symm)
    (center_mem_openCubeSet_of_subset D E hsub)
    (center_mem_openCubeSet_of_subset D (ancestor D n) (closedCube_subset_ancestor D n))

theorem nested_or_disjoint (D E : TriadicCube d) :
    (∃ n, E = ancestor D n ∧ closedCube D ⊆ closedCube E) ∨
      (∃ n, D = ancestor E n ∧ closedCube E ⊆ closedCube D) ∨
      Disjoint (Homogenization.openCubeSet D) (Homogenization.openCubeSet E) := by
  rcases le_total D.scale E.scale with hscale | hscale
  · rcases closedCube_subset_or_openCubeSet_disjoint D E hscale with hsub | hdis
    · left
      refine ⟨(E.scale - D.scale).toNat, ?_, hsub⟩
      apply eq_ancestor_of_scale_of_subset D E _ _ hsub
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hscale)]
      ring
    · exact Or.inr (Or.inr hdis)
  · rcases closedCube_subset_or_openCubeSet_disjoint E D hscale with hsub | hdis
    · right; left
      refine ⟨(D.scale - E.scale).toNat, ?_, hsub⟩
      apply eq_ancestor_of_scale_of_subset E D _ _ hsub
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hscale)]
      ring
    · exact Or.inr (Or.inr hdis.symm)

end

end CoarseDeGiorgi.Foundations.Triadic
