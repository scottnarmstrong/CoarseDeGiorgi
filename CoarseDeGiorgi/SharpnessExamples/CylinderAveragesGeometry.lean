module

public import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesDefs
public import CoarseDeGiorgi.Foundations.Euclid.Basic
public import CoarseDeGiorgi.Statements.SimplexCell

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

def cylinderRectLower {n : ℕ} (axisCenter axisRadius : ℝ)
    (center : Vec n) (tailRadius : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases (axisCenter - axisRadius) (fun i => center i - tailRadius)

def cylinderRectUpper {n : ℕ} (axisCenter axisRadius : ℝ)
    (center : Vec n) (tailRadius : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases (axisCenter + axisRadius) (fun i => center i + tailRadius)

/-- A coordinate rectangle with a possibly different axial half-width. -/
def cylinderRectangle {n : ℕ} (axisCenter axisRadius : ℝ)
    (center : Vec n) (tailRadius : ℝ) : Set (Vec (n + 1)) :=
  Set.pi Set.univ (fun i => Set.Ioo
    (cylinderRectLower axisCenter axisRadius center tailRadius i)
    (cylinderRectUpper axisCenter axisRadius center tailRadius i))

theorem mem_cylinderRectangle {n : ℕ} {axisCenter axisRadius tailRadius : ℝ}
    {center : Vec n} {x : Vec (n + 1)} :
    x ∈ cylinderRectangle axisCenter axisRadius center tailRadius ↔
      axisCenter - axisRadius < x 0 ∧ x 0 < axisCenter + axisRadius ∧
        ∀ i, center i - tailRadius < x i.succ ∧
          x i.succ < center i + tailRadius := by
  simp only [cylinderRectangle, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo]
  rw [Fin.forall_fin_succ]
  dsimp [cylinderRectLower, cylinderRectUpper]
  constructor
  · rintro ⟨⟨h0l, h0u⟩, ht⟩
    exact ⟨h0l, h0u, ht⟩
  · rintro ⟨h0l, h0u, ht⟩
    exact ⟨⟨h0l, h0u⟩, ht⟩

theorem cylinderRectangle_volume_toReal {n : ℕ} {axisCenter axisRadius tailRadius : ℝ}
    (hAxis : 0 ≤ axisRadius) (hTail : 0 ≤ tailRadius) (center : Vec n) :
    (volume (cylinderRectangle axisCenter axisRadius center tailRadius)).toReal =
      (2 * axisRadius) * (2 * tailRadius) ^ n := by
  rw [cylinderRectangle, Real.volume_pi_Ioo_toReal]
  · calc
      _ = (2 * axisRadius) *
          ∏ i : Fin n, (2 * tailRadius) := by
            rw [Fin.prod_univ_succ]
            congr 1
            · dsimp [cylinderRectLower, cylinderRectUpper]
              ring
            · apply Finset.prod_congr rfl
              intro i _
              dsimp [cylinderRectLower, cylinderRectUpper]
              ring
      _ = (2 * axisRadius) * (2 * tailRadius) ^ n := by
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro i
    refine Fin.cases ?_ ?_ i
    · dsimp [cylinderRectLower, cylinderRectUpper]
      linarith
    · intro j
      dsimp [cylinderRectLower, cylinderRectUpper]
      linarith

/-- Coordinates of two points in a triadic simplex cell differ by less than
the side length of its parent cube. -/
theorem cylinderSimplex_coord_diff {d k : ℕ} (eta : SimplexIndex d k)
    {x y : Vec d} (hx : x ∈ simplexCell k eta) (hy : y ∈ simplexCell k eta)
    (i : Fin d) :
    |x i - y i| < (3 : ℝ) ^ (-(k : ℤ)) := by
  let h : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let z : Vec d := fun j => h * (eta.1.1 j : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  change ∃ u : Vec d, x = z + (fun j => h * u j) ∧
    (∀ j, -(1 / 2 : ℝ) < u j ∧ u j < 1 / 2) ∧
    (∀ i j : Fin d, i < j → u (eta.1.2 i) < u (eta.1.2 j)) at hx
  change ∃ u : Vec d, y = z + (fun j => h * u j) ∧
    (∀ j, -(1 / 2 : ℝ) < u j ∧ u j < 1 / 2) ∧
    (∀ i j : Fin d, i < j → u (eta.1.2 i) < u (eta.1.2 j)) at hy
  rcases hx with ⟨u, rfl, hu, _⟩
  rcases hy with ⟨v, hxy, hv, _⟩
  have hdiff : |u i - v i| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hu i, hv i]
  rw [hxy]
  simp only [Pi.add_apply]
  have hcoord :
      (z i + h * u i) - (z i + h * v i) = h * (u i - v i) := by ring
  rw [hcoord, abs_mul, abs_of_pos hh]
  simpa [h] using (mul_lt_mul_of_pos_left hdiff hh)

theorem cylinderSimplex_volume_toReal {n k : ℕ} (eta : SimplexIndex (n + 1) k) :
    (volume (simplexCell k eta)).toReal =
      ((3 : ℝ) ^ (-(k : ℤ))) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  rw [CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.simplexCell_volume_real,
    CoarseDeGiorgi.triangulation_card]
  push_cast
  have hscale : ((3 : ℝ) ^ (-(k : ℤ))) ^ (n + 1) =
      ((3 : ℝ) ^ (k * (n + 1)))⁻¹ := by
    have hz : (3 : ℝ) ^ (-(k : ℤ)) = ((3 : ℝ) ^ k)⁻¹ := by
      simp [zpow_neg]
    rw [hz, inv_pow, ← pow_mul]
  rw [hscale]
  have hfact : (Nat.factorial (n + 1) : ℝ) ≠ 0 := by positivity
  field_simp [hfact]

theorem simplexCell_cylinder_inter_subset_rectangle {n k : ℕ}
    {epsilon : ℝ} {center : Vec n} {eta : SimplexIndex (n + 1) k}
    {base : Vec (n + 1)} (hbase : base ∈ simplexCell k eta) :
    simplexCell k eta ∩ averagesCylinder epsilon center ⊆
      cylinderRectangle (base 0) ((3 : ℝ) ^ (-(k : ℤ))) center epsilon := by
  intro x hx
  rw [mem_cylinderRectangle]
  refine ⟨?_, ?_, ?_⟩
  · have hcoord := cylinderSimplex_coord_diff eta hbase hx.1 0
    rcases abs_lt.mp hcoord with ⟨hlo, hhi⟩
    linarith
  · have hcoord := cylinderSimplex_coord_diff eta hbase hx.1 0
    rcases abs_lt.mp hcoord with ⟨hlo, hhi⟩
    linarith
  · intro i
    have hcoord := Sharpness.abs_transverse_coordinate_le
      (flatJoin 0 center - x) i.succ (by simp)
    have hcoord' : |center i - x i.succ| ≤
        Sharpness.transverseNorm (flatJoin 0 center - x) := by
      simpa [flatJoin] using hcoord
    have htube := lt_of_le_of_lt hcoord' hx.2.2
    rcases abs_lt.mp htube with ⟨hlo, hhi⟩
    constructor <;> linarith

private theorem cylinderRectangle_volume_ne_top {n : ℕ}
    (axisCenter axisRadius tailRadius : ℝ) (center : Vec n) :
    volume (cylinderRectangle axisCenter axisRadius center tailRadius) ≠ ⊤ := by
  rw [cylinderRectangle, Real.volume_pi_Ioo]
  exact ENNReal.prod_ne_top fun i hi => ENNReal.ofReal_ne_top

theorem cylinderSimplex_fraction_bounds {n k : ℕ} (epsilon : ℝ)
    (center : Vec n) (eta : SimplexIndex (n + 1) k) :
    0 ≤ cylinderFraction (simplexCell k eta) epsilon center ∧
      cylinderFraction (simplexCell k eta) epsilon center ≤ 1 := by
  rw [simplexCell_cylinderFraction_eq_source]
  have hVtop : volume (simplexCell k eta) ≠ ⊤ := by
    exact (CoarseDeGiorgi.simplexCell_isOpenBoundedConvexDomain k eta).isBoundedDomain.isBounded.measure_lt_top.ne
  have hVpos : 0 < (volume (simplexCell k eta)).toReal := by
    rw [cylinderSimplex_volume_toReal]
    positivity
  have hnum : (volume (simplexCell k eta ∩ averagesCylinder epsilon center)).toReal ≤
      (volume (simplexCell k eta)).toReal :=
    ENNReal.toReal_mono hVtop (measure_mono Set.inter_subset_left)
  constructor
  · exact div_nonneg ENNReal.toReal_nonneg (le_of_lt hVpos)
  · exact (div_le_one hVpos).2 hnum

theorem cylinderSimplex_fraction_coarse_bound {n k : ℕ} {epsilon : ℝ}
    (heps : 0 ≤ epsilon) (center : Vec n) (eta : SimplexIndex (n + 1) k) :
    cylinderFraction (simplexCell k eta) epsilon center ≤
      (Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ (n + 1) *
        (epsilon / ((3 : ℝ) ^ (-(k : ℤ))) ) ^ n := by
  obtain ⟨base, hbase⟩ := CoarseDeGiorgi.simplexCell_nonempty k eta
  let side : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let outer := cylinderRectangle (base 0) side center epsilon
  have hside : 0 < side := by dsimp [side]; positivity
  have hcontain : simplexCell k eta ∩ averagesCylinder epsilon center ⊆ outer := by
    exact simplexCell_cylinder_inter_subset_rectangle hbase
  have houterTop : volume outer ≠ ⊤ := by
    dsimp [outer]
    exact cylinderRectangle_volume_ne_top (base 0) side epsilon center
  have hnum : (volume (simplexCell k eta ∩ averagesCylinder epsilon center)).toReal ≤
      (volume outer).toReal := ENNReal.toReal_mono houterTop (measure_mono hcontain)
  have hVpos : 0 < (volume (simplexCell k eta)).toReal := by
    rw [cylinderSimplex_volume_toReal]
    positivity
  rw [simplexCell_cylinderFraction_eq_source]
  calc
    _ ≤ (volume outer).toReal / (volume (simplexCell k eta)).toReal :=
      div_le_div_of_nonneg_right hnum (le_of_lt hVpos)
    _ = (Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ (n + 1) *
        (epsilon / side) ^ n := by
      rw [cylinderRectangle_volume_toReal (le_of_lt hside) heps center,
        cylinderSimplex_volume_toReal]
      have hfact : (Nat.factorial (n + 1) : ℝ) ≠ 0 := by positivity
      field_simp [hside.ne', hfact]
      rw [show (3 : ℝ) ^ (-(k : ℤ)) = side by rfl]
      rw [pow_succ, pow_succ, div_pow]
      field_simp [pow_ne_zero n hside.ne']
      ring

theorem averagesCylinder_subset_outerRectangle {n : ℕ} {epsilon : ℝ}
    {center : Vec n} :
    averagesCylinder epsilon center ⊆
      cylinderRectangle 0 (1 / 2) center epsilon := by
  intro x hx
  rw [mem_cylinderRectangle]
  refine ⟨?_, ?_, ?_⟩
  · simpa [originCube] using (hx.1 0).1
  · simpa [originCube] using (hx.1 0).2
  · intro i
    have hcoord := Sharpness.abs_transverse_coordinate_le
      (flatJoin 0 center - x) i.succ (by simp)
    have hcoord' : |center i - x i.succ| ≤
        Sharpness.transverseNorm (flatJoin 0 center - x) := by
      simpa [flatJoin] using hcoord
    have htube := lt_of_le_of_lt hcoord' hx.2
    rcases abs_lt.mp htube with ⟨hlo, hhi⟩
    constructor <;> linarith

theorem smallRectangle_subset_averagesCylinder {n : ℕ} {epsilon radius : ℝ}
    {center : Vec n} (heps4 : epsilon < 1 / 4)
    (hcenter : ∀ i, |center i| ≤ 1 / 4)
    (hr : 0 < radius) (hrEps : radius ≤ epsilon)
    (hEuclidean : Real.sqrt ((n + 1 : ℕ) : ℝ) * radius < epsilon) :
    cylinderRectangle 0 (1 / 2) center radius ⊆
      averagesCylinder epsilon center := by
  intro x hx
  rw [mem_cylinderRectangle] at hx
  rcases hx with ⟨hx0l, hx0u, hxtail⟩
  have hcube : x ∈ originCube 1 := by
    intro i
    refine Fin.cases ?_ ?_ i
    · constructor <;> linarith
    · intro j
      have hcenterj := abs_le.mp (hcenter j)
      constructor <;> linarith [hxtail j, hrEps.trans_lt heps4]
  have hsup : ‖Sharpness.transversePart (flatJoin 0 center - x)‖ ≤ radius := by
    apply (pi_norm_le_iff_of_nonneg hr.le).2
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [Sharpness.transversePart]
      exact hr.le
    · intro j
      have hcoord : |center j - x j.succ| < radius := by
        rw [abs_lt]
        constructor <;> linarith [hxtail j]
      simpa [Sharpness.transversePart, flatJoin, Real.norm_eq_abs] using hcoord.le
  have htube : Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon := by
    calc
      _ = CoarseDeGiorgi.Foundations.Euclid.eNorm2
          (Sharpness.transversePart (flatJoin 0 center - x)) := rfl
      _ ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) *
          ‖Sharpness.transversePart (flatJoin 0 center - x)‖ :=
        CoarseDeGiorgi.Foundations.Euclid.eNorm2_le_sqrt_mul_norm _
      _ ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * radius :=
        mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
      _ < epsilon := hEuclidean
  exact ⟨hcube, htube⟩

theorem outerRectangle_subset_originCube {n : ℕ} {epsilon : ℝ} {center : Vec n}
    (heps4 : epsilon < 1 / 4) (hcenter : ∀ i, |center i| ≤ 1 / 4) :
    cylinderRectangle 0 (1 / 2) center epsilon ⊆ originCube 1 := by
  intro x hx i
  rw [mem_cylinderRectangle] at hx
  rcases hx with ⟨hx0l, hx0u, hxtail⟩
  refine Fin.cases ?_ ?_ i
  · constructor <;> linarith
  · intro j
    have hc := abs_le.mp (hcenter j)
    constructor <;> linarith [hxtail j]

theorem averagesCylinder_volume_bounds {n : ℕ} (epsilon : ℝ) (center : Vec n)
    (heps : 0 < epsilon) (heps4 : epsilon < 1 / 4)
    (hcenter : ∀ i, |center i| ≤ 1 / 4) :
    (epsilon / ((n + 1 : ℕ) : ℝ)) ^ n ≤
        (volume (averagesCylinder epsilon center)).toReal ∧
      (volume (averagesCylinder epsilon center)).toReal ≤ (2 * epsilon) ^ n := by
  let D : ℝ := (n + 1 : ℕ)
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast Nat.le_add_left 1 n
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hsqrt : Real.sqrt D ≤ D := by
    have hsquare : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hDpos.le
    nlinarith [Real.sqrt_nonneg D, hsquare]
  let radius : ℝ := epsilon / (2 * D)
  have hradius : 0 < radius := by dsimp [radius]; positivity
  have hradiusEps : radius ≤ epsilon := by
    dsimp [radius]
    apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
    nlinarith [heps, hD]
  have hsmallEuclidean : Real.sqrt ((n + 1 : ℕ) : ℝ) * radius < epsilon := by
    calc
      _ ≤ D * radius := by
        apply mul_le_mul_of_nonneg_right hsqrt
        positivity
      _ = epsilon / 2 := by dsimp [D, radius]; field_simp
      _ < epsilon := by linarith
  have hsmall : cylinderRectangle 0 (1 / 2) center radius ⊆
      averagesCylinder epsilon center :=
    smallRectangle_subset_averagesCylinder heps4 hcenter hradius hradiusEps
      hsmallEuclidean
  have houter : averagesCylinder epsilon center ⊆
      cylinderRectangle 0 (1 / 2) center epsilon :=
    averagesCylinder_subset_outerRectangle
  have hcubeTop : volume (originCube (d := n + 1) 1) ≠ ⊤ := by
    rw [CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one]
    simp
  have hEtop : volume (averagesCylinder epsilon center) ≠ ⊤ :=
    ne_top_of_le_ne_top hcubeTop (measure_mono Set.inter_subset_left)
  have houterCube : cylinderRectangle 0 (1 / 2) center epsilon ⊆ originCube 1 :=
    outerRectangle_subset_originCube heps4 hcenter
  have houterTop : volume (cylinderRectangle 0 (1 / 2) center epsilon) ≠ ⊤ :=
    ne_top_of_le_ne_top hcubeTop (measure_mono houterCube)
  have hlower := ENNReal.toReal_mono hEtop (measure_mono hsmall)
  have hupper := ENNReal.toReal_mono houterTop (measure_mono houter)
  rw [cylinderRectangle_volume_toReal (by norm_num) (le_of_lt hradius) center] at hlower
  rw [cylinderRectangle_volume_toReal (by norm_num) (le_of_lt heps) center] at hupper
  constructor
  · have hformula : (2 * (1 / 2 : ℝ)) * (2 * radius) ^ n =
        (epsilon / D) ^ n := by
      dsimp [radius]
      have hDne : D ≠ 0 := ne_of_gt hDpos
      field_simp [hDne]
    rw [hformula] at hlower
    simpa [D] using hlower
  · simpa using hupper

end CoarseDeGiorgi.SharpnessExamples
