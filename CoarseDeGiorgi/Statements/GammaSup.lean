module

public import CoarseDeGiorgi.Statements.GammaRec
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.RBoundaryParam
public import CoarseDeGiorgi.Statements.RStarParam

@[expose] public section

namespace CoarseDeGiorgi

/-- `γ₄ := 2 max{ γ₃ / (r_∂^* - 2), γ₃ / (2 r^*/r - 2) }` (the paragraph before Proposition `p.energy.to.sup`):
the power of `(ρ₂ - ρ₁)⁻¹` in `energy_to_supremum`. -/
noncomputable def gammaSup (d : ℕ) (p q s t : ℝ) : ℝ :=
  2 * max (gammaRec d p q s t / (rBoundaryParam (d := d) q t - 2))
    (gammaRec d p q s t / (2 * rStarParam (d := d) q t / paramR q - 2))

end CoarseDeGiorgi
