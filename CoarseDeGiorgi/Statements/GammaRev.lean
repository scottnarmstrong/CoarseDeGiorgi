module

public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.GammaLoc
public import CoarseDeGiorgi.Statements.ParamTheta

@[expose] public section

namespace CoarseDeGiorgi

/-- `γ₅ := (1-t) + γ₁ (1-t) / θ`: the power of `(ρ₂ - ρ₁)⁻¹` in one reverse inequality
(Lemma `l.positive.negative.moments`). -/
noncomputable def gammaRev (d : ℕ) (p q s t : ℝ) : ℝ :=
  alphaParam t + gammaLoc p q t * alphaParam t / paramTheta d p q s t

end CoarseDeGiorgi
