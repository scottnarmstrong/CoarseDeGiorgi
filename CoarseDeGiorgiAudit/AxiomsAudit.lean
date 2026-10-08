module

public import CoarseDeGiorgi.Statements.LocalBoundedness
public import CoarseDeGiorgi.Statements.WeakHarnackRange
public import CoarseDeGiorgi.Statements.WeakHarnack
public import CoarseDeGiorgi.Statements.Harnack
public import CoarseDeGiorgi.Statements.MomentBoundsLebesgue
public import CoarseDeGiorgi.Statements.MomentBoundsBesov
public import CoarseDeGiorgi.Statements.MomentBoundsSobolev
public import CoarseDeGiorgi.Statements.ClassicalMomentsConverse
public import CoarseDeGiorgi.Statements.Sharpness
public import CoarseDeGiorgi.Statements.OptimalPowers
public import CoarseDeGiorgi.Statements.WeakHarnackSharpness
public import CoarseDeGiorgi.Statements.CubicalSimplicialEquivalence
public import CoarseDeGiorgi.Statements.LocalBoundednessCubical
public import CoarseDeGiorgi.Statements.WeakHarnackCubical
public import CoarseDeGiorgi.Statements.HarnackCubical
public import CoarseDeGiorgi.Statements.LocalBoundednessSobolev
public import CoarseDeGiorgi.Statements.HarnackSobolev
public import CoarseDeGiorgiAudit.Solution.Harnack
public import CoarseDeGiorgiAudit.Solution.WeakHarnack
public import CoarseDeGiorgiAudit.Solution.ResponseQuadraticForms
public import CoarseDeGiorgiAudit.Solution.HarnackLpLq
public import CoarseDeGiorgiAudit.Solution.WeakHarnackLpLq
public import CoarseDeGiorgiAudit.Solution.LocalBoundednessLpLq
public import CoarseDeGiorgiAudit.Solution.HarnackUniform
public import CoarseDeGiorgiAudit.Solution.WeakHarnackUniform
public import CoarseDeGiorgiAudit.Solution.LocalBoundednessUniform
public import CoarseDeGiorgiAudit.Solution.HarnackBesov
public import CoarseDeGiorgiAudit.Solution.WeakHarnackBesov
public import CoarseDeGiorgiAudit.Solution.LocalBoundednessBesov
public import CoarseDeGiorgiAudit.Solution.HarnackSobolev
public import CoarseDeGiorgiAudit.Solution.LocalBoundednessSobolev
public import CoarseDeGiorgiAudit.Solution.Sharpness
public import CoarseDeGiorgiAudit.Solution.SharpnessPolynomial
public import CoarseDeGiorgiAudit.Solution.SharpnessWeakHarnack

/-!
# Axiom dependencies of the main results

Building this module prints the axiom dependencies of the main theorems of the
library and of the theorems proved by the comparator solutions in
`CoarseDeGiorgiAudit/Solution/`. Each must report exactly the three standard
foundational axioms of Mathlib:

```
'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

For long names Lean wraps the list over several lines. The module is not
imported by any other module; it belongs to the `CoarseDeGiorgiAudit`
library, which is not a default target. After `lake build CoarseDeGiorgiAudit`,
print the report with `lake env lean CoarseDeGiorgiAudit/AxiomsAudit.lean`.
-/

@[expose] public section

/-! ## Main theorems of the library -/

#print axioms CoarseDeGiorgi.local_boundedness
#print axioms CoarseDeGiorgi.weak_harnack_range
#print axioms CoarseDeGiorgi.weak_harnack
#print axioms CoarseDeGiorgi.harnack
#print axioms CoarseDeGiorgi.moment_bounds_lebesgue
#print axioms CoarseDeGiorgi.moment_bounds_besov
#print axioms CoarseDeGiorgi.moment_bounds_sobolev
#print axioms CoarseDeGiorgi.classical_moments_converse
#print axioms CoarseDeGiorgi.sharpness
#print axioms CoarseDeGiorgi.optimal_powers
#print axioms CoarseDeGiorgi.weak_harnack_sharpness
#print axioms CoarseDeGiorgi.cubical_simplicial_equivalence
#print axioms CoarseDeGiorgi.local_boundedness_cubical
#print axioms CoarseDeGiorgi.weak_harnack_cubical
#print axioms CoarseDeGiorgi.harnack_cubical
#print axioms CoarseDeGiorgi.local_boundedness_sobolev
#print axioms CoarseDeGiorgi.harnack_sobolev

/-! ## Theorems of the comparator solutions -/

#print axioms CoarseDeGiorgiAudit.Harnack.harnack
#print axioms CoarseDeGiorgiAudit.WeakHarnack.weakHarnack
#print axioms CoarseDeGiorgiAudit.ResponseQuadraticForms.responseQuadraticForms
#print axioms CoarseDeGiorgiAudit.HarnackLpLq.harnackLpLq
#print axioms CoarseDeGiorgiAudit.WeakHarnackLpLq.weakHarnackLpLq
#print axioms CoarseDeGiorgiAudit.LocalBoundednessLpLq.localBoundednessLpLq
#print axioms CoarseDeGiorgiAudit.HarnackUniform.harnackUniform
#print axioms CoarseDeGiorgiAudit.WeakHarnackUniform.weakHarnackUniform
#print axioms CoarseDeGiorgiAudit.LocalBoundednessUniform.localBoundednessUniform
#print axioms CoarseDeGiorgiAudit.HarnackBesov.harnackBesov
#print axioms CoarseDeGiorgiAudit.WeakHarnackBesov.weakHarnackBesov
#print axioms CoarseDeGiorgiAudit.LocalBoundednessBesov.localBoundednessBesov
#print axioms CoarseDeGiorgiAudit.HarnackSobolev.harnackSobolev
#print axioms CoarseDeGiorgiAudit.LocalBoundednessSobolev.localBoundednessSobolev
#print axioms CoarseDeGiorgiAudit.Sharpness.sharpness
#print axioms CoarseDeGiorgiAudit.SharpnessPolynomial.sharpnessPolynomial
#print axioms CoarseDeGiorgiAudit.SharpnessWeakHarnack.sharpnessWeakHarnack
