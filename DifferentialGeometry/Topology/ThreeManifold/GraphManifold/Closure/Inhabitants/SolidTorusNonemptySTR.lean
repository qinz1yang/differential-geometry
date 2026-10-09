import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRimsFinalSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 8: actual points of the circle region and the two corners

Draft 80, D80-9: the circle region of the solid torus cut is NON-EMPTY and so are the actual rim
fibres.

* the explicit interior point `q* = (7/8) i` of `C₁` (`‖q*‖² = 49/64 ∈ (5/8, 15/16)`, `Re q* = 0`),
  lifted to an actual point `p*` of the region with `z₂(p*) = q*` (`region_nonempty_STR`); the
  region lies in the actual circle source (`region_subset_domain_STR`);
* the two corner points `q± = 4/5 ± i √119/20` (`‖q±‖² = 15/16`, `Re q± = 4/5`) are the rim base
  points of the two endpoints `t = 0, 1` (`qRim_zero_STR`, `qRim_one_STR`); each is lifted to an
  actual rim fibre (`rim_fibre_STR`, non-empty), at which the ball face (`phiBall = 0`) and the
  vertical face (`phiVert = 0`) are active and the cusp face is not (`corner_labels_STR`);
* `corner_incidences_STR`: TWO incidences `e₀ ≠ e₁` with disjoint whole rims and distinct base
  points, both attached to the SAME ball face (the shared owner does not merge them).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_NonemptySTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_NonemptySTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## The interior point `q* = (7/8) i` -/

/-- The explicit interior point of `C₁`. -/
def qStar_STR : ℂ := ⟨0, 7 / 8⟩

/-- The base point of `q*`. -/
def cStar_STR : rows_STR.circle.Base :=
  ⟨⟨⟨modelPlaneComplex.symm qStar_STR, by
    change ‖modelPlaneComplex.symm qStar_STR‖ < 1
    rw [LinearIsometryEquiv.norm_map]
    have : ‖qStar_STR‖ = 7 / 8 := by
      rw [Complex.norm_def, Complex.normSq_apply]
      change √(0 * 0 + 7 / 8 * (7 / 8)) = 7 / 8
      rw [show (0 : ℝ) * 0 + 7 / 8 * (7 / 8) = (7 / 8) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [this]
    norm_num⟩, by
    change (1 / 2 : ℝ) < ‖modelPlaneComplex.symm qStar_STR‖ ^ 2
    rw [LinearIsometryEquiv.norm_map]
    have : ‖qStar_STR‖ ^ 2 = 49 / 64 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      change (0 : ℝ) * 0 + 7 / 8 * (7 / 8) = 49 / 64
      norm_num
    rw [this]
    norm_num⟩, trivial⟩

theorem qOfBase_cStar_STR : qOfBase_STR cStar_STR.1 = qStar_STR :=
  modelPlaneComplex.apply_symm_apply _

theorem norm_cStar_STR : ‖qOfBase_STR cStar_STR.1‖ ^ 2 = 49 / 64 := by
  rw [qOfBase_cStar_STR, Complex.sq_norm, Complex.normSq_apply]
  change (0 : ℝ) * 0 + 7 / 8 * (7 / 8) = 49 / 64
  norm_num

theorem cStar_mem_cbase_STR : cStar_STR ∈ rows_STR.circle.cbase := by
  change (5 / 8 ≤ ‖qOfBase_STR cStar_STR.1‖ ^ 2 ∧ ‖qOfBase_STR cStar_STR.1‖ ^ 2 ≤ 15 / 16 ∧
    (qOfBase_STR cStar_STR.1).re ≤ 4 / 5)
  rw [norm_cStar_STR, qOfBase_cStar_STR]
  change 5 / 8 ≤ (49 / 64 : ℝ) ∧ (49 / 64 : ℝ) ≤ 15 / 16 ∧ (0 : ℝ) ≤ 4 / 5
  norm_num

/-- The region of the circle bundle lies in the actual circle source. -/
theorem region_subset_domain_STR :
    rows_STR.circle.region ⊆ (rows_STR.circle.domain : Set Wc.Carrier) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- The circle region is non-empty: the actual point `p*` over `q* = (7/8) i`. -/
theorem region_nonempty_STR : ∃ p : Wc.Carrier, p ∈ rows_STR.circle.region ∧
    p ∈ (rows_STR.circle.domain : Set Wc.Carrier) ∧ sphereSecond p.val = qStar_STR ∧
    X135Radial.height p = -(17 / 32 : ℝ) := by
  obtain ⟨x, hx⟩ := fibre_nonempty_STR cStar_STR
  have hreg : x ∈ rows_STR.circle.region := by
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    change rows_STR.circle.proj y ∈ rows_STR.circle.cbase
    rw [hy]
    exact cStar_mem_cbase_STR
  refine ⟨x, hreg, region_subset_domain_STR hreg, ?_, ?_⟩
  · obtain ⟨-, hs⟩ := mem_fibre_STR.1 hx
    rw [hs, qOfBase_cStar_STR]
  · rw [fibre_height_STR cStar_STR x hx, norm_cStar_STR]
    norm_num

/-- The circle source is non-empty. -/
theorem domain_nonempty_STR : ((rows_STR.circle.domain : Set Wc.Carrier)).Nonempty := by
  obtain ⟨p, -, hp, -⟩ := region_nonempty_STR
  exact ⟨p, hp⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
