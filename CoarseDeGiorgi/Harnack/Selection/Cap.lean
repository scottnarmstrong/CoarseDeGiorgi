import CoarseDeGiorgi.Assembly.HybridFractional
import CoarseDeGiorgi.Weighted.Truncation.PositivePart

namespace CoarseDeGiorgi.Harnack.Selection

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The capped positive part `min ((v - c)₊) N` (uncapped if `N = ⊤`) used in the surface
selection (Proposition `p.good.radius`). -/
abbrev selectionCap {d : ℕ} (c : ℝ) (N : ℝ≥0∞) (v : Vec d → ℝ) : Vec d → ℝ :=
  fun x => if N = ⊤ then max (v x - c) 0 else min (max (v x - c) 0) N.toReal

/-- Its source gradient: a strict interval indicator for finite caps and the positive-part
gradient when the upper cap is infinite. -/
abbrev selectionCapGradient {d : ℕ} (c : ℝ) (N : ℝ≥0∞)
    (v : Vec d → ℝ) (G : Vec d → Vec d) : Vec d → Vec d :=
  fun x => if N = ⊤ then {x | c < v x}.indicator G x
    else {x | c < v x ∧ v x < c + N.toReal}.indicator G x

private theorem min_max_sub_max {c N t : ℝ} (hN : 0 ≤ N) :
    min (max (t - c) 0) N = max (t - c) 0 - max (t - (c + N)) 0 := by
  by_cases h₀ : t ≤ c
  · rw [max_eq_right (sub_nonpos.mpr h₀), min_eq_left (by linarith),
      max_eq_right (sub_nonpos.mpr (by linarith))]
    simp
  · by_cases h₁ : t ≤ c + N
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h₀)),
        min_eq_left (by linarith), max_eq_right (sub_nonpos.mpr (by linarith))]
      simp
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h₀)),
        min_eq_right (by linarith), max_eq_left (sub_nonneg.mpr (by linarith))]
      linarith

/-- The capped positive part belongs to the weighted space. For a finite cap its gradient is
the source's strict band indicator, and for an infinite cap it is the positive-part gradient. -/
theorem selectionCap_memH1a {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a a (originCube 1) v G) (c : ℝ) (N : ℝ≥0∞) (hN : N ≠ 0) :
    MemH1a a (originCube 1) (selectionCap c N v)
      (selectionCapGradient c N v G) := by
  let hV := Assembly.hybrid_unitCube_domain (d := d)
  by_cases htop : N = ⊤
  · unfold selectionCap selectionCapGradient
    simp only [ite_eq_left htop]
    exact Weighted.MemH1a.max_sub_const hV.1 hV.2 ha hv c
  · have hNr : 0 < N.toReal := ENNReal.toReal_pos hN htop
    let v₁ := fun x => max (v x - c) 0
    let v₂ := fun x => max (v x - (c + N.toReal)) 0
    have hv₁ : MemH1a a (originCube 1) v₁ ({x | c < v x}.indicator G) := by
      exact Weighted.MemH1a.max_sub_const hV.1 hV.2 ha hv c
    have hv₂ : MemH1a a (originCube 1) v₂
        ({x | c + N.toReal < v x}.indicator G) := by
      exact Weighted.MemH1a.max_sub_const hV.1 hV.2 ha hv (c + N.toReal)
    have hvsub := Weighted.MemH1a.add hV.1 hV.2 ha hv₁
      (Weighted.MemH1a.neg hV.1 hV.2 ha hv₂)
    have hval : (selectionCap c N v) =ᵐ[volume.restrict (originCube 1)] (v₁ - v₂) := by
      filter_upwards with x
      simpa [selectionCap, v₁, v₂, htop] using min_max_sub_max hNr.le
    have hzero := Weighted.MemH1a.gradient_zero_on_level hV.1 hV.2 ha hv (c + N.toReal)
    have hgrad : ({x | c < v x}.indicator G - {x | c + N.toReal < v x}.indicator G)
        =ᵐ[volume.restrict (originCube 1)]
          ({x | c < v x ∧ v x < c + N.toReal}.indicator G) := by
      filter_upwards [hzero] with x hx
      by_cases hlo : c < v x
      · by_cases heq : v x = c + N.toReal
        · have hz : G x = 0 := by simpa [heq] using hx
          simp [heq, hz]
        · by_cases hhi : c + N.toReal < v x
          · have hnot : ¬ v x < c + N.toReal := not_lt_of_ge hhi.le
            simp [hlo, hhi, hnot]
          · have hlt : v x < c + N.toReal := lt_of_le_of_ne (le_of_not_gt hhi) heq
            simp [hlo, hhi, hlt]
      · have hnotUpper : ¬ c + N.toReal < v x := by linarith [hNr]
        simp [hlo, hnotUpper]
    have hgrad' : ({x | c < v x}.indicator G + -{x | c + N.toReal < v x}.indicator G)
        =ᵐ[volume.restrict (originCube 1)]
          ({x | c < v x ∧ v x < c + N.toReal}.indicator G) := by
      simpa only [sub_eq_add_neg] using hgrad
    have hpair := Weighted.MemH1a.congr_ae hvsub hval.symm hgrad'
    have hgradDef : selectionCapGradient c N v G =
        {x | c < v x ∧ v x < c + N.toReal}.indicator G := by
      funext x
      dsimp [selectionCapGradient]
      rw [ite_eq_right htop]
    rw [hgradDef]
    exact hpair

/-- The capped gradient's energy density is pointwise no larger than the original density;
this is the input needed to compare the corresponding surface maximal functions. -/
theorem selectionCap_density_le {d : ℕ} (a : CoeffField d)
    (v : Vec d → ℝ) (G : Vec d → Vec d)
    (c : ℝ) (N : ℝ≥0∞) :
    ∀ x,
      ENNReal.ofReal (vecDot (selectionCapGradient c N v G x)
        (matVecMul (a x) (selectionCapGradient c N v G x))) ≤
      ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))) := by
  intro x
  by_cases htop : N = ⊤
  · by_cases hband : c < v x
    · have hsame : selectionCapGradient c N v G x = G x := by
        simp [selectionCapGradient, htop, hband]
      rw [hsame]
    · have hzero : selectionCapGradient c N v G x = 0 := by
        simp [selectionCapGradient, htop, hband]
      rw [hzero, matVecMul_zero, vecDot_zero_left, ENNReal.ofReal_zero]
      exact bot_le
  · by_cases hband : c < v x ∧ v x < c + N.toReal
    · have hsame : selectionCapGradient c N v G x = G x := by
        simp [selectionCapGradient, htop, hband]
      rw [hsame]
    · have hzero : selectionCapGradient c N v G x = 0 := by
        simp [selectionCapGradient, htop, hband]
      rw [hzero, matVecMul_zero, vecDot_zero_left, ENNReal.ofReal_zero]
      exact bot_le

end
end CoarseDeGiorgi.Harnack.Selection
