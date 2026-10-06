import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRimsSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialFibreFaces

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 2: the circle fibres, `rim_fibre` and `edge_region`

* `mem_fibre_STR`: `x ∈ fibre c ↔ x ∈ circle domain ∧ z₂(x) = q(c)` for the restricted circle
  bundle `rows_STR.circle`; `fibre_height_STR`: the height on a fibre is `1 - 2‖q(c)‖²`;
  `fibre_nonempty_STR`.
* `rimBase_STR`, `rimBase_smooth_STR`, `rim_fibre_STR` (the whole rim over `t` equals the whole
  circle fibre over `rimBase t`), and `edge_region_STR` (`M^edge ∩ M₃ = V`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_RimFibreSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_RimFibreSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## The fibres of the restricted circle bundle -/

theorem mem_fibre_STR {c : rows_STR.circle.Base} {x : Wc.Carrier} :
    x ∈ rows_STR.circle.fibre c ↔ ∃ _ : x ∈ X135Radial.radialCircleDomain,
      sphereSecond x.val = qOfBase_STR c.1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y.val ∈ X135Radial.radialCircleDomain :=
      (stageGeometry_STR ballZeroDomainsL_STR).circle.restrictParent_le _ y.2
    refine ⟨hy', ?_⟩
    have h1 : (X135Radial.radialCircleProjection ⟨y.val, hy'⟩) = c.1 :=
      congrArg Subtype.val hy
    have h2 := X135Radial.radialCircleProjection_complex ⟨y.val, hy'⟩
    rw [h1] at h2
    exact h2.symm
  · rintro ⟨hx, hs⟩
    refine ⟨⟨x, (stageGeometry_STR ballZeroDomainsL_STR).circle.mem_restrictParent_of hx
      trivial⟩, ?_, rfl⟩
    refine Subtype.ext (Subtype.ext (Subtype.ext (modelPlaneComplex.injective ?_)))
    have h2 := X135Radial.radialCircleProjection_complex ⟨x, hx⟩
    change modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val =
      modelPlaneComplex c.1.val.val
    rw [h2]
    exact hs

theorem fibre_height_STR (c : rows_STR.circle.Base) (x : Wc.Carrier)
    (hx : x ∈ rows_STR.circle.fibre c) :
    X135Radial.height x = 1 - 2 * ‖qOfBase_STR c.1‖ ^ 2 := by
  obtain ⟨-, hs⟩ := mem_fibre_STR.1 hx
  have h := norm_second_sq_STR x
  rw [hs] at h
  linarith

theorem fibre_re_STR (c : rows_STR.circle.Base) (x : Wc.Carrier)
    (hx : x ∈ rows_STR.circle.fibre c) : uW_STR x = (qOfBase_STR c.1).re := by
  obtain ⟨-, hs⟩ := mem_fibre_STR.1 hx
  change (sphereSecond x.val).re = _
  rw [hs]

theorem fibre_nonempty_STR (c : rows_STR.circle.Base) : ∃ x, x ∈ rows_STR.circle.fibre c :=
  ⟨(X135Radial.radialFibrePoint c.1).val, mem_fibre_STR.2
    ⟨(X135Radial.radialFibrePoint c.1).2, by
      have h2 := X135Radial.radialCircleProjection_complex (X135Radial.radialFibrePoint c.1)
      have h3 := congrArg (fun b : X135Radial.radialCircleBase => modelPlaneComplex b.val.val)
        (X135Radial.radialFibrePoint_projection c.1)
      exact h2.symm.trans h3⟩⟩

/-! ## The rim base -/

/-- The rim base of the edge base point `c`. -/
def rimBase_STR (c : rows_STR.edge.Base) : rows_STR.circle.Base :=
  ⟨rimPoint_STR (coordE_STR c), trivial⟩

theorem rimBase_smooth_STR :
    ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase_STR rows_STR.edge.cbase := by
  have h : ContMDiff (𝓡 1) (𝓡 2) ∞ (fun c : Base1_STR => rimPoint_STR (coordE_STR c)) := by
    have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun c : Base1_STR => 0 + 1 * c.val 0) :=
      contMDiff_coord_STR 1 0
    have hc' : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun c : Base1_STR => coordE_STR c) := by
      convert hc using 1
      funext c
      simp [coordE_STR]
    exact contMDiff_rimPoint_STR.comp hc'
  exact ((contMDiff_subtypeVal_comp_iff
    (⊤ : TopologicalSpace.Opens X135Radial.radialCircleBase) rimBase_STR).mp h).contMDiffOn

theorem qOfBase_rimBase_STR (c : rows_STR.edge.Base) :
    qOfBase_STR (rimBase_STR c).1 = qRim_STR (coordE_STR c) :=
  qOfBase_rimPoint_STR _

/-- **`rim_fibre`**: the whole rim over `t` is the whole circle fibre over its rim base point. -/
theorem rim_fibre_STR (c : rows_STR.edge.Base) :
    rows_STR.edge.rim c = rows_STR.circle.fibre (rimBase_STR c) := by
  have hr : rows_STR.edge.rim c = rimSet_STR (coordE_STR c) := rim_eq_STR _ c
  rw [hr]
  ext y
  rw [mem_fibre_STR, qOfBase_rimBase_STR]
  constructor
  · rintro ⟨hy, ht, hs⟩
    have hn := norm_sphereFirst_sq_add y.val
    have hnorm : ‖sphereSecond y.val‖ = rr_STR := by
      have h1 : ‖sphereSecond y.val‖ ^ 2 = rr_STR ^ 2 := by rw [rr_sq_STR]; linarith
      have h2 := norm_nonneg (sphereSecond y.val)
      nlinarith [rr_pos_STR]
    have hz : zOf_STR (sphereSecond y.val) = zRim_STR (coordE_STR c) := by
      have hc := cR_pos_STR kap_lt_rr_STR
      have h1 : tOf_STR (sphereSecond y.val) = coordE_STR c := ht
      rw [tOf_STR, hnorm] at h1
      rw [zRim_STR]
      field_simp at h1 ⊢
      linarith
    have hh := height_eq_of_first_STR y
    refine ⟨⟨by rw [hh]; linarith, by rw [hh, hs]; norm_num⟩, ?_⟩
    have := qOf_zOf_STR hy.2
    rw [hnorm, hz] at this
    exact this.symm
  · rintro ⟨hy, hs⟩
    have hn := norm_sphereFirst_sq_add y.val
    have hnorm : ‖sphereSecond y.val‖ = rr_STR := by rw [hs]; exact norm_qRim_STR _
    have hs1 : ‖sphereFirst y.val‖ ^ 2 = 1 / 16 := by
      have h := rr_sq_STR
      rw [hnorm] at hn
      linarith
    have hp : y ∈ edgeParent_STR := by
      refine ⟨by rw [hs1]; norm_num, ?_⟩
      rw [hs]
      exact re_lt_norm_qRim_STR _
    exact ⟨hp, by rw [hs]; exact tOf_qRim_STR _, hs1⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
