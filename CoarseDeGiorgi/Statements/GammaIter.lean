module

public import CoarseDeGiorgi.Statements.ChiParam
public import CoarseDeGiorgi.Statements.GammaRev
public import CoarseDeGiorgi.Statements.ParamR

@[expose] public section

namespace CoarseDeGiorgi

/-- `γ₆ := γ₅ r χ / (χ - 1)` with `χ := r^*/r`: the power of `(ρ₂ - ρ₁)⁻¹` after
iteration (Lemma `l.moment.iterations`). -/
noncomputable def gammaIter (d : ℕ) (p q s t : ℝ) : ℝ :=
  gammaRev d p q s t * paramR q * chiParam d q t / (chiParam d q t - 1)

end CoarseDeGiorgi
