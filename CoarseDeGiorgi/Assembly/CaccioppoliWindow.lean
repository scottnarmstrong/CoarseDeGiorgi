import CoarseDeGiorgi.Assembly.CaccioppoliHole
import CoarseDeGiorgi.Assembly.CaccioppoliReal

namespace CoarseDeGiorgi.Assembly

open scoped ENNReal

/-- Finite ENNReal data: collar absorption followed by the committed hole-filling lemma. -/
theorem caccioppoli_finite_window {C : ℝ≥0∞} {D θ γ m : ℝ}
    (hC : C ≠ ⊤) (hD : 0 < D) (hθ : 0 < θ) (hγ : θ ≤ γ) (hm : 0 ≤ m) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (f : ℝ → ℝ≥0∞) (ρ R : ℝ) (Θ Λ N : ℝ≥0∞),
      Monotone f → ρ < R → R - ρ ≤ 1 → f R < ⊤ →
      Θ ≠ ⊤ → Λ ≠ ⊤ → N ≠ ⊤ →
      (∀ ρ' R' : ℝ, ρ ≤ ρ' → ρ' < R' → R' ≤ R →
        ∀ n : ℤ, (3 : ℝ) ^ n ≤ (R' - ρ') / D →
          f ρ' ≤ C * (ENNReal.ofReal (R' - ρ')).rpow (-γ) *
            (Θ.rpow (1 / 2) * (ENNReal.ofReal ((3 : ℝ) ^ n)).rpow θ * f R' +
              Λ.rpow (1 / 2) * (ENNReal.ofReal ((3 : ℝ) ^ n)).rpow (-m) * N *
                (f R').rpow (1 / 2))) →
      f ρ ≤ ENNReal.ofReal (K * (R - ρ) ^ (-(2 * γ + 2 * γ * m / θ)) *
        Λ.toReal * (1 + Θ.toReal) ^ (m / θ) * N.toReal ^ 2) := by
  let κ := 2 * γ + 2 * γ * m / θ
  let ε := (2 : ℝ) ^ (-κ - 2)
  have hε : 0 < ε := Real.rpow_pos_of_pos (by norm_num) _
  have hγ0 : 0 < γ := lt_of_lt_of_le hθ hγ
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  obtain ⟨B, hB, habs⟩ := caccioppoli_absorption C.toReal_nonneg hD hθ hγ hm hε
  let K := 2 * (2 : ℝ) ^ κ * B + 1
  refine ⟨K, by
    dsimp [K]
    have : 0 ≤ 2 * (2 : ℝ) ^ κ * B := by positivity
    linarith, ?_⟩
  intro f ρ R Θ Λ N hf hρR hδ1 hfR hΘ hΛ hN hsurf
  let g : ℝ → ℝ≥0∞ := fun r => f (min R r)
  have hgm : Monotone g := fun r s hrs => hf (min_le_min le_rfl hrs)
  have hgf (r : ℝ) : g r ≠ ⊤ := ne_top_of_le_ne_top hfR.ne (hf (min_le_left R r))
  have hge (r : ℝ) (hr : r ≤ R) : g r = f r := by dsimp [g]; rw [min_eq_right hr]
  let A := B * Λ.toReal * (1 + Θ.toReal) ^ (m / θ) * N.toReal ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hstep : ∀ r s : ℝ, ρ ≤ r → r < s → s ≤ R →
      g r ≤ ENNReal.ofReal (2 * ε) * g s + ENNReal.ofReal (A * (s - r) ^ (-κ)) := by
    intro r s hρr hrs hsR
    have hrR := hrs.le.trans hsR
    have hfr : f r ≠ ⊤ := (hge r hrR) ▸ hgf r
    have hfs : f s ≠ ⊤ := (hge s hsR) ▸ hgf s
    have hd : 0 < s - r := sub_pos.mpr hrs
    have hd1 : s - r ≤ 1 := by linarith only [hρr, hsR, hδ1]
    have hb := habs (s - r) Θ.toReal Λ.toReal N.toReal (f s).toReal (f r).toReal
      hd hd1 Θ.toReal_nonneg Λ.toReal_nonneg N.toReal_nonneg (f s).toReal_nonneg
      (fun n hn => caccioppoli_surface_toReal hC hΘ hΛ hN hfs hd
        (zpow_pos (by norm_num) n) (hsurf r s hρr hrs hsR n hn))
    have hb' : (f r).toReal ≤ 2 * ε * (f s).toReal + A * (s - r) ^ (-κ) := by
      convert hb using 1; dsimp [A, κ]; ring
    rw [hge r hrR, hge s hsR]
    calc
      f r = ENNReal.ofReal (f r).toReal := (ENNReal.ofReal_toReal hfr).symm
      _ ≤ ENNReal.ofReal (2 * ε * (f s).toReal + A * (s - r) ^ (-κ)) :=
        ENNReal.ofReal_le_ofReal hb'
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfs]
  have hh := caccioppoli_hole_filling hgm hρR hA hκ
    (by simpa only [g, min_self] using hfR) hstep
  rw [hge ρ hρR.le] at hh
  have hc : 2 * (2 : ℝ) ^ κ * B ≤ K := by dsimp [K]; linarith
  calc
    f ρ ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ κ) * ENNReal.ofReal A *
        ENNReal.ofReal ((R - ρ) ^ (-κ)) := hh
    _ = ENNReal.ofReal ((2 * (2 : ℝ) ^ κ * B) * (R - ρ) ^ (-κ) *
        Λ.toReal * (1 + Θ.toReal) ^ (m / θ) * N.toReal ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [A]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right hc
      all_goals positivity)


end CoarseDeGiorgi.Assembly
