module

public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import Mathlib.Tactic

@[expose] public section

namespace CoarseDeGiorgi.Assembly

open scoped ENNReal

/-- The finite one-surface inequality is the same inequality over the reals. -/
theorem caccioppoli_surface_toReal {C Θ Λ N E F : ℝ≥0∞} {δ h γ θ m : ℝ}
    (hC : C ≠ ⊤) (hΘ : Θ ≠ ⊤) (hΛ : Λ ≠ ⊤) (hN : N ≠ ⊤) (hE : E ≠ ⊤)
    (hδ : 0 < δ) (hh : 0 < h)
    (hb : F ≤ C * (ENNReal.ofReal δ).rpow (-γ) *
      (Θ.rpow (1 / 2) * (ENNReal.ofReal h).rpow θ * E +
        Λ.rpow (1 / 2) * (ENNReal.ofReal h).rpow (-m) * N * E.rpow (1 / 2))) :
    F.toReal ≤ C.toReal * δ ^ (-γ) *
      (Real.sqrt Θ.toReal * h ^ θ * E.toReal +
        Real.sqrt Λ.toReal * h ^ (-m) * N.toReal * Real.sqrt E.toReal) := by
  have hδ0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hh0 : ENNReal.ofReal h ≠ 0 := (ENNReal.ofReal_pos.mpr hh).ne'
  have hδp : (ENNReal.ofReal δ).rpow (-γ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ0 ENNReal.ofReal_ne_top
  have hhp (r : ℝ) : (ENNReal.ofReal h).rpow r ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hh0 ENNReal.ofReal_ne_top
  have ht1 : Θ.rpow (1 / 2) * (ENNReal.ofReal h).rpow θ * E ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΘ) (hhp θ)) hE
  have ht2 : Λ.rpow (1 / 2) * (ENNReal.ofReal h).rpow (-m) * N * E.rpow (1 / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΛ) (hhp (-m))) hN)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE)
  have hright : C * (ENNReal.ofReal δ).rpow (-γ) *
      (Θ.rpow (1 / 2) * (ENNReal.ofReal h).rpow θ * E +
        Λ.rpow (1 / 2) * (ENNReal.ofReal h).rpow (-m) * N * E.rpow (1 / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hδp) (ENNReal.add_ne_top.mpr ⟨ht1, ht2⟩)
  have hr := ENNReal.toReal_mono hright hb
  simp only [ENNReal.toReal_mul] at hr
  rw [ENNReal.toReal_add ht1 ht2] at hr
  simp only [ENNReal.toReal_mul, ENNReal.rpow_eq_pow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofReal hh.le, ← Real.sqrt_eq_rpow] at hr
  exact hr


end CoarseDeGiorgi.Assembly
