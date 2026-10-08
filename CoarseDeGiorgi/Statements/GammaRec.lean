import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.RBoundaryParam
import CoarseDeGiorgi.Statements.RStarParam
import CoarseDeGiorgi.Statements.SigmaUpper

namespace CoarseDeGiorgi

/-- `γ₃ := max{ 1 + 1/p + ((1-t) + 1/r) r_∂^* + 2 γ₁ σ / θ , 2 (1-t) r^* / r }`
(`e.recurrence.exponent`): the power of `(ρ₂ - ρ₁)⁻¹` in the two-level recurrence (Proposition `p.two.level.recurrence`). -/
noncomputable def gammaRec (d : ℕ) (p q s t : ℝ) : ℝ :=
  max (1 + 1 / p + (alphaParam t + 1 / paramR q) * rBoundaryParam (d := d) q t +
      2 * gammaLoc p q t * sigmaUpper d p s / paramTheta d p q s t)
    (2 * alphaParam t * rStarParam (d := d) q t / paramR q)

end CoarseDeGiorgi
