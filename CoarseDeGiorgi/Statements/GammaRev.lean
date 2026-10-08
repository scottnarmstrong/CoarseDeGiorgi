import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.ParamTheta

namespace CoarseDeGiorgi

/-- `γ₅ := (1-t) + γ₁ (1-t) / θ`: the power of `(ρ₂ - ρ₁)⁻¹` in one reverse inequality
(Lemma `l.positive.negative.moments`). -/
noncomputable def gammaRev (d : ℕ) (p q s t : ℝ) : ℝ :=
  alphaParam t + gammaLoc p q t * alphaParam t / paramTheta d p q s t

end CoarseDeGiorgi
