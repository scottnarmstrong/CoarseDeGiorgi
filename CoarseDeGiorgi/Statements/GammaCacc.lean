import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.SigmaLower

namespace CoarseDeGiorgi

/-- `γ₂ := 2 γ₁ (1 - σ_*) / θ` (`e.localization.exponents`): the power of
`(ρ₂ - ρ₁)⁻¹` in the Caccioppoli inequality (Proposition `p.cg.caccioppoli`). -/
noncomputable def gammaCacc (d : ℕ) (p q s t : ℝ) : ℝ :=
  2 * gammaLoc p q t * (1 - sigmaLower d q t) / paramTheta d p q s t

end CoarseDeGiorgi
