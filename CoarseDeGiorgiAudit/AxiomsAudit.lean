import CoarseDeGiorgi.Statements.LocalBoundedness
import CoarseDeGiorgi.Statements.WeakHarnackRange
import CoarseDeGiorgi.Statements.WeakHarnack
import CoarseDeGiorgi.Statements.Harnack
import CoarseDeGiorgi.Statements.MomentBoundsLebesgue
import CoarseDeGiorgi.Statements.MomentBoundsBesov
import CoarseDeGiorgi.Statements.MomentBoundsSobolev
import CoarseDeGiorgi.Statements.ClassicalMomentsConverse
import CoarseDeGiorgi.Statements.Sharpness
import CoarseDeGiorgi.Statements.OptimalPowers
import CoarseDeGiorgi.Statements.WeakHarnackSharpness
import CoarseDeGiorgi.Statements.CubicalSimplicialEquivalence
import CoarseDeGiorgi.Statements.LocalBoundednessCubical
import CoarseDeGiorgi.Statements.WeakHarnackCubical
import CoarseDeGiorgi.Statements.HarnackCubical
import CoarseDeGiorgi.Statements.LocalBoundednessSobolev
import CoarseDeGiorgi.Statements.HarnackSobolev
import CoarseDeGiorgiAudit.Solution.Harnack
import CoarseDeGiorgiAudit.Solution.WeakHarnack
import CoarseDeGiorgiAudit.Solution.ResponseQuadraticForms
import CoarseDeGiorgiAudit.Solution.HarnackLpLq
import CoarseDeGiorgiAudit.Solution.WeakHarnackLpLq
import CoarseDeGiorgiAudit.Solution.LocalBoundednessLpLq
import CoarseDeGiorgiAudit.Solution.HarnackUniform
import CoarseDeGiorgiAudit.Solution.WeakHarnackUniform
import CoarseDeGiorgiAudit.Solution.LocalBoundednessUniform
import CoarseDeGiorgiAudit.Solution.HarnackBesov
import CoarseDeGiorgiAudit.Solution.WeakHarnackBesov
import CoarseDeGiorgiAudit.Solution.LocalBoundednessBesov
import CoarseDeGiorgiAudit.Solution.HarnackSobolev
import CoarseDeGiorgiAudit.Solution.LocalBoundednessSobolev
import CoarseDeGiorgiAudit.Solution.Sharpness
import CoarseDeGiorgiAudit.Solution.SharpnessPolynomial
import CoarseDeGiorgiAudit.Solution.SharpnessWeakHarnack

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
