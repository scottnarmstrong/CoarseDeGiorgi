module

public import CoarseDeGiorgiAudit.DefsResponses
public import CoarseDeGiorgi.Statements.GridOffset
public import CoarseDeGiorgi.Statements.Triangulation
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.Simplex
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.UpperDirectionalResponseSol
public import CoarseDeGiorgi.Statements.LowerDirectionalResponse
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.Contrast

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit

theorem gridOffset_eq {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    gridOffset k j = CoarseDeGiorgi.gridOffset k j := rfl

theorem triangulation_eq {d : ℕ} (k : ℕ) :
    triangulation (d := d) k = CoarseDeGiorgi.triangulation (d := d) k := rfl

theorem simplexIndex_eq (d k : ℕ) :
    SimplexIndex d k = CoarseDeGiorgi.SimplexIndex d k := rfl

theorem simplex_eq {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    simplex n π z = CoarseDeGiorgi.simplex n π z := rfl

theorem simplexCell_eq {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    simplexCell k η = CoarseDeGiorgi.simplexCell k η := rfl

theorem paramTheta_eq (d : ℕ) (p q s t : ℝ) :
    paramTheta d p q s t = CoarseDeGiorgi.paramTheta d p q s t := rfl

theorem upperDirectionalResponseSol_eq {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) :
    upperDirectionalResponseSol a V e =
      CoarseDeGiorgi.upperDirectionalResponseSol a V e := rfl

theorem lowerDirectionalResponse_eq {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) :
    lowerDirectionalResponse a V e =
      CoarseDeGiorgi.lowerDirectionalResponse a V e := rfl

theorem upperCellAverageOf_eq {d : ℕ}
    (A : (k : ℕ) → SimplexIndex d k → Mat d) (k : ℕ) (p : ℝ) :
    upperCellAverageOf A k p =
      ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖A k ⟨η.1, η.2⟩‖ p) /
        ((triangulation (d := d) k).card : ℝ) := rfl

theorem lowerCellAverageOf_eq {d : ℕ}
    (B : (k : ℕ) → SimplexIndex d k → Mat d) (k : ℕ) (q : ℝ) :
    lowerCellAverageOf B k q =
      ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖B k ⟨η.1, η.2⟩‖ q) /
        ((triangulation (d := d) k).card : ℝ) := rfl

theorem upperMomentOf_eq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (s p : ℝ) (hs : 0 < s) (hp : 1 ≤ p) :
    upperMomentOf (fun k η => CoarseDeGiorgi.upperResponseOnCell k a ha η)
        s p hs hp =
      CoarseDeGiorgi.upperMoment a ha s p hs hp := rfl

theorem lowerMomentOf_eq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (t q : ℝ) (ht : 0 < t) (hq : 1 ≤ q) :
    lowerMomentOf (fun k η => CoarseDeGiorgi.lowerResponseInvOnCell k a ha η)
        t q ht hq =
      CoarseDeGiorgi.lowerMoment a ha t q ht hq := rfl

theorem contrastOf_eq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (s t p q : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    contrastOf
        (fun k η => CoarseDeGiorgi.upperResponseOnCell k a ha η)
        (fun k η => CoarseDeGiorgi.lowerResponseInvOnCell k a ha η)
        s t p q hs ht hp hq =
      CoarseDeGiorgi.contrast a ha s t p q hs ht hp hq := rfl

end CoarseDeGiorgiAudit
