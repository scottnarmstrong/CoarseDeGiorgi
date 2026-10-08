module

public import CoarseDeGiorgi.Foundations.Reconstruction.Representatives

/-! # The exact reconstruction statement in dimension zero -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The zero-dimensional branch uses the `Statements/` definitions and the same
quantifiers as the reconstruction target. Its constant is `1`. -/
theorem fractional_reconstruction_zero_dim {α r : ℝ}
    (_hα0 : 0 < α) (_hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (z : Fin 0 → ℤ) (w : Vec 0 → ℝ) (Dw : Vec 0 → Vec 0),
        HasWeakGradientOn (CoarseDeGiorgi.auxCube m z) w Dw →
        IntegrableOn w (CoarseDeGiorgi.auxCube m z) volume →
        IntegrableOn Dw (CoarseDeGiorgi.auxCube m z) volume →
        MemLp w (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) →
        CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w ≤
          ENNReal.ofReal C *
            ∑' k : {k : ℤ // m ≤ k},
              ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
                eLpNorm (fun x => CoarseDeGiorgi.euclidNorm
                  (CoarseDeGiorgi.auxAverage m k.1 z Dw x))
                  (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro m z w Dw hweak hw hDw hmem
  rw [← fracSeminorm_eq_statement,
    fracSeminorm_zero_dim _ α (lt_trans (by norm_num) hr) w]
  exact bot_le

end

end CoarseDeGiorgi.Foundations.Reconstruction
