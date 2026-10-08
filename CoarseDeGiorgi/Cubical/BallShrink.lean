import Homogenization.Geometry.ConvexDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Combination

/-! # Boundary layers of a convex body containing a sup-norm ball -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- Shrinking a convex body towards the center of an inscribed sup-norm ball. -/
theorem layer_volume_le {S : Set (Vec d)} (hS : IsOpenBoundedConvexDomain S)
    (c₀ : Vec d) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ y : Vec d, (∀ i, |y i - c₀ i| < ρ) → y ∈ S)
    {F : Set (Vec d)} (hFS : F ⊆ S) {θ : ℝ} (hθ : 0 < θ)
    (hF : ∀ x ∈ F, ∃ y, y ∉ S ∧ ∀ i, |x i - y i| < θ * ρ) :
    (volume F).toReal ≤ (d * θ) * (volume S).toReal := by
  have hSfin : volume S ≠ ⊤ := hS.isBoundedDomain.isBounded.measure_lt_top.ne
  rcases le_or_gt 1 θ with h1 | h1
  · -- trivial case
    have hd : (1 : ℝ) ≤ d ∨ d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact Or.inr h
      · exact Or.inl (by exact_mod_cast h)
    rcases hd with hd | rfl
    · calc (volume F).toReal ≤ (volume S).toReal :=
            ENNReal.toReal_mono hSfin (measure_mono hFS)
        _ = 1 * 1 * (volume S).toReal := by ring
        _ ≤ (d * θ) * (volume S).toReal := by
            apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
            nlinarith
    · -- dimension zero: F empty or the whole space point; volume of a subset of a point
      -- in `Fin 0 → ℝ` the hypothesis hF forces F = ∅ since S is the whole (single point) space
      have : F = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
        obtain ⟨y, hy, _⟩ := hF x hx
        apply hy
        have : y = x := Subsingleton.elim _ _
        rw [this]; exact hFS hx
      simp [this]
  · set H : Set (Vec d) := AffineMap.homothety c₀ (1 - θ) '' S with hH
    have hθ1 : 0 < 1 - θ := by linarith
    have hc₀ : c₀ ∈ S := hball c₀ (fun i => by simpa using hρ)
    have hHS : H ⊆ S := by
      rintro _ ⟨w, hw, rfl⟩
      have := hS.convex hw hc₀ (a := 1 - θ) (b := θ) hθ1.le hθ.le (by ring)
      convert this using 1
      simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      ext i; simp; ring
    have hHopen : IsOpen H := (AffineMap.homothety_isOpenMap c₀ (1 - θ) hθ1.ne') S hS.isOpen
    have hFH : F ⊆ S \ H := by
      intro x hx
      refine ⟨hFS hx, ?_⟩
      rintro ⟨w, hw, hwx⟩
      obtain ⟨y, hy, hxy⟩ := hF x hx
      apply hy
      have hx' : x = (1 - θ) • w + θ • c₀ := by
        rw [← hwx]; simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
        ext i; simp; ring
      let u : Vec d := c₀ + θ⁻¹ • (y - x)
      have hu : u ∈ S := by
        apply hball
        intro i
        simp only [u, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_sub_cancel_left]
        rw [abs_mul, abs_inv, abs_of_pos hθ, inv_mul_lt_iff₀ hθ]
        rw [abs_sub_comm]; exact hxy i
      have := hS.convex hw hu (a := 1 - θ) (b := θ) hθ1.le hθ.le (by ring)
      convert this using 1
      ext i
      have hxi : x i = (1 - θ) * w i + θ * c₀ i := by rw [hx']; simp
      simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      rw [hxi]; ring
    have hvolH : volume H = ENNReal.ofReal ((1 - θ) ^ d) * volume S := by
      have hfr : Module.finrank ℝ (Vec d) = d := by simp
      rw [hH, Measure.addHaar_image_homothety, abs_pow, abs_of_pos hθ1, hfr]
    have h2 : volume F ≤ volume S - volume H :=
      (measure_mono hFH).trans (measure_sdiff hHS hHopen.measurableSet.nullMeasurableSet
        (ne_top_of_le_ne_top hSfin (measure_mono hHS))).le
    have h3 : (volume F).toReal ≤ (volume S).toReal - (volume H).toReal := by
      have := ENNReal.toReal_mono (ENNReal.sub_ne_top hSfin) h2
      rwa [ENNReal.toReal_sub_of_le (measure_mono hHS) hSfin] at this
    rw [hvolH, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h3
    have hb : 1 - (d : ℝ) * θ ≤ (1 - θ) ^ d := by
      have := one_add_mul_le_pow (a := -θ) (by linarith) d
      simpa [sub_eq_add_neg, mul_comm] using this
    have hv : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hb hv]

end CoarseDeGiorgi.Cubical
