module

public import CoarseDeGiorgi.Foundations.FractionalSobolev.SurfaceEmbeddingSum
public import CoarseDeGiorgi.Statements.DnpvTheorem6_7UnitCube

@[expose] public section

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

/-- The facewise critical estimate, with one constant also covering the L² consequence. -/
theorem embedding_critical_successor {n : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) (hcritical : α * r < (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, (1/2 : ℝ) ≤ τ → τ ≤ 1 →
      ∀ g : Vec (n+1) → ℝ, Measurable g →
        eLpNorm g (ENNReal.ofReal (dnpvCriticalExponent n α r)) (surfaceMeasure τ) ≤
          ENNReal.ofReal C * surfaceFracNorm τ α r g ∧
        (2 ≤ dnpvCriticalExponent n α r → eLpNorm g 2 (surfaceMeasure τ) ≤
          ENNReal.ofReal C * surfaceFracNorm τ α r g) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hq := (critical_parameters hα0 hr.le hcritical).2.2.2.1
  obtain ⟨C₀, hC₀, h67⟩ := CoarseDeGiorgi.dnpv_theorem_6_7_unitCube n α r hα0 hα1 hr.le hcritical
  let B : ℝ := ((2 ^ n : ℝ) * (2 ^ n : ℝ)) ^ (1/r)
  let D : ℝ := 2 * (n+1 : ℕ)
  let C₁ : ℝ := D * C₀ * B
  let C : ℝ := C₁ * (1+D)
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hC₁ : 0 < C₁ := mul_pos (mul_pos hD hC₀) hB
  have hC : 0 < C := mul_pos hC₁ (by dsimp [D]; positivity)
  have hBcast : ENNReal.ofReal B = ((2 ^ n : ℝ≥0∞) * (2 ^ n : ℝ≥0∞)) ^ (1/r) := by
    dsimp [B]
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hDcast : ENNReal.ofReal D = (2 * (n+1) : ℝ≥0∞) := by
    dsimp [D]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_natCast]
    norm_num
  have hCcast : ENNReal.ofReal C₁ = ENNReal.ofReal D * ENNReal.ofReal C₀ * ENNReal.ofReal B := by
    rw [ENNReal.ofReal_mul (mul_pos hD hC₀).le, ENNReal.ofReal_mul hD.le]
  have hC₁C : C₁ ≤ C := by dsimp [C]; nlinarith only [hC₁, hD]
  have hDC : D * C₁ ≤ C := by dsimp [C]; nlinarith only [hC₁]
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 g hg
  by_cases htop : surfaceFracNorm τ α r g = ⊤
  · simp only [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne', le_top, implies_true, and_self]
  have hF : surfaceFracNorm τ α r g < ⊤ := lt_top_iff_ne_top.mpr htop
  have hface (i : Fin (n+1)) (pos : Bool) :
      eLpNorm g (ENNReal.ofReal (dnpvCriticalExponent n α r)) (cubeFaceMeasure τ i pos) ≤
        ENNReal.ofReal C₀ * ENNReal.ofReal B * surfaceFracNorm τ α r g := by
    let f := g ∘ embeddingFaceChart τ i pos
    have hfn : fracNorm (dnpvUnitCube n) α r f ≤ ENNReal.ofReal B * surfaceFracNorm τ α r g := by
      rw [hBcast]
      exact embedding_chart_norm_le hτ hτ1 hr0 (by positivity) i pos hg
    have hfinite : fracNorm (dnpvUnitCube n) α r f < ⊤ := hfn.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF)
    have hmem : MemDnpvSobolev (dnpvUnitCube n) α r f :=
      ⟨(embedding_lp_le_fracNorm _ _ hr0 f).trans_lt hfinite,
        (embedding_semi_le_fracNorm _ _ hr0 f).trans_lt hfinite⟩
    calc
      _ ≤ eLpNorm g (ENNReal.ofReal (dnpvCriticalExponent n α r))
          (Measure.map (embeddingFaceChart τ i pos) (volume.restrict (dnpvUnitCube n))) :=
        eLpNorm_mono_measure g (embeddingFaceChart_measure_bounds hτ hτ1 i pos).1
      _ = eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n α r)) (volume.restrict (dnpvUnitCube n)) :=
        eLpNorm_map_measure hg.aestronglyMeasurable (embeddingFaceChart_measurable τ i pos).aemeasurable
      _ ≤ ENNReal.ofReal C₀ * fracNorm (dnpvUnitCube n) α r f := h67 f hmem
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul' le_rfl hfn
  have hcrit : eLpNorm g (ENNReal.ofReal (dnpvCriticalExponent n α r)) (surfaceMeasure τ) ≤
      ENNReal.ofReal C₁ * surfaceFracNorm τ α r g := by
    calc
      _ ≤ ∑ i : Fin (n+1), ∑ pos : Bool,
          eLpNorm g (ENNReal.ofReal (dnpvCriticalExponent n α r)) (cubeFaceMeasure τ i pos) :=
        embedding_surface_lp_le_sum hq hg τ
      _ ≤ ∑ _i : Fin (n+1), ∑ _pos : Bool,
          ENNReal.ofReal C₀ * ENNReal.ofReal B * surfaceFracNorm τ α r g :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun pos _ => hface i pos))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin,
          nsmul_eq_mul, hCcast, hDcast, Nat.cast_add, Nat.cast_one]
        ring
  constructor
  · exact hcrit.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC₁C) le_rfl)
  · intro htwo
    have h2 : eLpNorm g 2 (surfaceMeasure τ) ≤ ENNReal.ofReal D *
        eLpNorm g (ENNReal.ofReal (dnpvCriticalExponent n α r)) (surfaceMeasure τ) := by
      rw [hDcast]
      simpa only [Nat.cast_add, Nat.cast_one] using
        embedding_surface_ltwo_le (by omega : 1 ≤ n+1) htwo hτ1 hg
    calc
      _ ≤ ENNReal.ofReal D * (ENNReal.ofReal C₁ * surfaceFracNorm τ α r g) :=
        h2.trans (mul_le_mul' le_rfl hcrit)
      _ = ENNReal.ofReal (D * C₁) * surfaceFracNorm τ α r g := by
        rw [ENNReal.ofReal_mul hD.le, mul_assoc]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hDC) le_rfl

/-- The critical surface embedding (Lemma `l.critical.trace.embedding`), with no added premises. -/
theorem critical_surface_embedding_proved {d : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r)
    (hcritical : α * r < (d : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧
        ∀ τ : ℝ, (1 / 2 : ℝ) ≤ τ → τ ≤ 1 →
        ∀ g : Vec d → ℝ, Measurable g →
          eLpNorm g
              (ENNReal.ofReal (((d : ℝ) - 1) * r /
                ((d : ℝ) - 1 - α * r))) (surfaceMeasure τ) ≤
            ENNReal.ofReal C * surfaceFracNorm τ α r g ∧
          (2 ≤ ((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r) →
            eLpNorm g 2 (surfaceMeasure τ) ≤
              ENNReal.ofReal C * surfaceFracNorm τ α r g) := by
  have hd : d ≠ 0 := by
    intro hz
    have hpos := mul_pos hα0 (lt_trans zero_lt_one hr)
    simp only [hz, Nat.cast_zero] at hcritical
    linarith only [hpos, hcritical]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have hc : α * r < (n : ℝ) := by simpa only [Nat.cast_succ, add_sub_cancel_right] using hcritical
  simpa only [dnpvCriticalExponent, Nat.cast_succ, add_sub_cancel_right] using
    embedding_critical_successor hα0 hα1 hr hc

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
