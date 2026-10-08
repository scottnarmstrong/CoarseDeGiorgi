module

public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.SurfaceTraceLimits

/-! # Pass selected trace control through a pairing bound -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Pass an extended-valued exterior pairing bound to its sharp real bound.
Only eventual finiteness of the approximating trace norms is needed. -/
theorem pairing_abs_eventually_close_of_ennreal_trace_bounds
    (C c₁ c₂ S₀ L₀ : ℝ≥0∞)
    (hC : C < ⊤) (hc₁ : c₁ < ⊤) (hc₂ : c₂ < ⊤)
    (hS₀ : S₀ < ⊤) (hL₀ : L₀ < ⊤)
    (S L : ℕ → ℝ≥0∞)
    (htrace : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      S i ≤ S₀ + ENNReal.ofReal ε ∧ L i ≤ L₀ + ENNReal.ofReal ε)
    (B : ℕ → ℝ)
    (hpair : ∀ i, ENNReal.ofReal |B i| ≤ C * (c₁ * S i + c₂ * L i)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      |B i| ≤ (C * (c₁ * S₀ + c₂ * L₀)).toReal + ε := by
  intro ε hε
  let δ : ℝ := ε / (C.toReal * (c₁.toReal + c₂.toReal) + 1)
  have hden : 0 < C.toReal * (c₁.toReal + c₂.toReal) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [htrace δ hδ] with i hi
  have hSbound : S₀ + ENNReal.ofReal δ < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hS₀, ENNReal.ofReal_lt_top⟩
  have hLbound : L₀ + ENNReal.ofReal δ < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hL₀, ENNReal.ofReal_lt_top⟩
  have hSi := hi.1.trans_lt hSbound
  have hLi := hi.2.trans_lt hLbound
  have hboundFinite : C * (c₁ * S i + c₂ * L i) < ⊤ := by
    exact ENNReal.mul_lt_top hC
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hc₁ hSi,
        ENNReal.mul_lt_top hc₂ hLi⟩)
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hboundFinite.ne).mp (hpair i)
  rw [ENNReal.toReal_mul, ENNReal.toReal_add
    (ENNReal.mul_lt_top hc₁ hSi).ne (ENNReal.mul_lt_top hc₂ hLi).ne,
    ENNReal.toReal_mul, ENNReal.toReal_mul] at hreal
  have hSr := ENNReal.toReal_mono hSbound.ne hi.1
  have hLr := ENNReal.toReal_mono hLbound.ne hi.2
  rw [ENNReal.toReal_add hS₀.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hδ.le] at hSr
  rw [ENNReal.toReal_add hL₀.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hδ.le] at hLr
  have hbase : (C * (c₁ * S₀ + c₂ * L₀)).toReal =
      C.toReal * (c₁.toReal * S₀.toReal + c₂.toReal * L₀.toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_add
      (ENNReal.mul_lt_top hc₁ hS₀).ne (ENNReal.mul_lt_top hc₂ hL₀).ne,
      ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [hbase]
  calc
    |B i| ≤ C.toReal * (c₁.toReal * (S i).toReal + c₂.toReal * (L i).toReal) := hreal
    _ ≤ C.toReal * (c₁.toReal * (S₀.toReal + δ) +
        c₂.toReal * (L₀.toReal + δ)) := by gcongr
    _ = C.toReal * (c₁.toReal * S₀.toReal + c₂.toReal * L₀.toReal) +
        C.toReal * (c₁.toReal + c₂.toReal) * δ := by ring
    _ ≤ C.toReal * (c₁.toReal * S₀.toReal + c₂.toReal * L₀.toReal) + ε := by
      have hδeq : (C.toReal * (c₁.toReal + c₂.toReal) + 1) * δ = ε := by
        dsimp only [δ]
        exact mul_div_cancel₀ _ hden.ne'
      have hle : C.toReal * (c₁.toReal + c₂.toReal) * δ ≤
          (C.toReal * (c₁.toReal + c₂.toReal) + 1) * δ := by
        gcongr
        exact le_add_of_nonneg_right zero_le_one
      exact add_le_add_right (hle.trans_eq hδeq) _

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
