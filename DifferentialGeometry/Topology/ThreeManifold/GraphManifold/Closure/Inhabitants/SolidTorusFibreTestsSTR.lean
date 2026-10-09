import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusFaceFnsSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 4: vertical faces, `edge_region`, fibre / face tests

* `mem_vertLike_STR`: the vertical face (and the whole vertical face of the component) is
  `{u ≤ κ, h = -7/8}`; `edge_region_STR : M^edge ∩ M₃ = V`.
* `mem_cbase_STR`: `q ∈ C₁` iff the three face functions are `≤ 0`.
* `fibre_cusp_iff_STR`, `fibre_ball_iff_STR`, `fibre_vert_iff_STR`: the whole circle fibre lies in
  the cusp face / the ball face / the whole vertical face iff the face function vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_FibreTestsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_FibreTestsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## The vertical face -/

theorem mem_vertLike_STR (T : Set Base1_STR) (hT : T = Subtype.val ⁻¹' edgeC2_STR)
    {x : Wc.Carrier} :
    x ∈ Subtype.val '' {y : rows_STR.edge.source | rows_STR.edge.proj y ∈ T ∧
      rows_STR.edge.height y = rows_STR.edge.level} ↔
      uW_STR x ≤ 4 / 5 ∧ X135Radial.height x = -(7 / 8 : ℝ) := by
  subst hT
  constructor
  · rintro ⟨y, ⟨hc, hh⟩, rfl⟩
    have hy : y.val ∈ edgeParent_STR :=
      (stageGeometry_STR ballZeroDomainsL_STR).edge.restrictParent_le _ y.2
    have hc' : edgeProj_STR ⟨y.val, hy⟩ ∈ edgeC2_STR := hc
    have h0 : tOf_STR (sphereSecond y.val.val) ∈ Icc (0 : ℝ) 1 := by
      rw [edgeProj_eq_single_STR hy] at hc'
      simpa [edgeC2_STR] using hc'
    have hh' : ‖sphereFirst y.val.val‖ ^ 2 = 1 / 16 := hh
    refine ⟨?_, ?_⟩
    · have := (t_mem_iff_STR hy).1 h0
      exact this
    · rw [height_eq_of_first_STR]
      linarith
  · rintro ⟨hu, hh⟩
    have hs : ‖sphereFirst x.val‖ ^ 2 = 1 / 16 := by
      rw [height_eq_of_first_STR] at hh
      linarith
    have hy : x ∈ edgeParent_STR := mem_edgeParent_of_STR hu hh.le
    refine ⟨⟨x, (stageGeometry_STR ballZeroDomainsL_STR).edge.mem_restrictParent_of hy trivial⟩,
      ⟨?_, hs⟩, rfl⟩
    have h1 := (t_mem_iff_STR hy).2 hu
    change edgeProj_STR ⟨x, hy⟩ ∈ edgeC2_STR
    rw [edgeProj_eq_single_STR hy]
    simpa [edgeC2_STR] using h1

theorem mem_vertical_STR {x : Wc.Carrier} :
    x ∈ rows_STR.edge.vertical ↔ uW_STR x ≤ 4 / 5 ∧ X135Radial.height x = -(7 / 8 : ℝ) :=
  mem_vertLike_STR (Subtype.val ⁻¹' edgeC2_STR) rfl

theorem mem_wholeVertical_STR (C : rows_STR.edge.EdgeBaseComponent) {x : Wc.Carrier} :
    x ∈ rows_STR.edge.wholeVertical C ↔
      uW_STR x ≤ 4 / 5 ∧ X135Radial.height x = -(7 / 8 : ℝ) := by
  have hC : C.1 = (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := by
    rw [actualComponent_eq_STR C]
    exact cbaseComp_val_STR
  exact mem_vertLike_STR C.1 hC

theorem edge_region_STR : (cutChoice_STR ballZeroDomainsL_STR).edgeSet ∩
    (cutChoice_STR ballZeroDomainsL_STR).M₃ = rows_STR.edge.vertical := by
  ext p
  rw [mem_vertical_STR, M3_eq_STR, edgeSet_eq_STR]
  constructor
  · rintro ⟨⟨hu, hh⟩, ⟨-, h1, -⟩⟩
    exact ⟨hu, le_antisymm hh h1⟩
  · rintro ⟨hu, hh⟩
    exact ⟨⟨hu, hh.le⟩, hu, hh.ge, by rw [hh]; norm_num⟩

/-! ## The base `C₁` and the fibre tests -/

theorem re_q_STR (c : rows_STR.circle.Base) : (qOfBase_STR c.1).re = reL_STR (vOf_STR c) := rfl

theorem mem_cbase_STR {c : rows_STR.circle.Base} :
    c ∈ rows_STR.circle.cbase ↔ phiCusp_STR c ≤ 0 ∧ phiVert_STR c ≤ 0 ∧ phiBall_STR c ≤ 0 := by
  have hn := norm_q_sq_STR c
  have hr := re_q_STR c
  change (5 / 8 ≤ ‖qOfBase_STR c.1‖ ^ 2 ∧ ‖qOfBase_STR c.1‖ ^ 2 ≤ 15 / 16 ∧
    (qOfBase_STR c.1).re ≤ 4 / 5) ↔ _
  rw [hn, hr]
  simp only [phiCusp_STR, phiVert_STR, phiBall_STR, gCusp_STR, gVert_STR, gBall_STR]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩

theorem fibre_cusp_iff_STR {c : rows_STR.circle.Base} :
    rows_STR.circle.fibre c ⊆ rows_STR.slimPieces.residualSet cuspRes_STR ↔ phiCusp_STR c = 0 := by
  have hn := norm_q_sq_STR c
  rw [rows_residualSet_cusp_STR]
  simp only [phiCusp_STR, gCusp_STR]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := fibre_nonempty_STR c
    have h1 : X135Radial.height x = -(1 / 4 : ℝ) := h hx
    rw [fibre_height_STR c x hx] at h1
    linarith
  · intro h x hx
    change X135Radial.height x = -(1 / 4 : ℝ)
    rw [fibre_height_STR c x hx]
    linarith

theorem fibre_ball_iff_STR {c : rows_STR.circle.Base} :
    rows_STR.circle.fibre c ⊆ rows_STR.slimPieces.residualSet ballRes_STR ↔ phiBall_STR c = 0 := by
  have hr := re_q_STR c
  rw [rows_residualSet_ball_STR]
  simp only [phiBall_STR, gBall_STR]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := fibre_nonempty_STR c
    have h1 : uW_STR x = 4 / 5 := h hx
    rw [fibre_re_STR c x hx, hr] at h1
    linarith
  · intro h x hx
    change uW_STR x = 4 / 5
    rw [fibre_re_STR c x hx, hr]
    linarith

theorem fibre_vert_iff_STR {c : rows_STR.circle.Base} (hc : c ∈ rows_STR.circle.cbase)
    (C : rows_STR.edge.EdgeBaseComponent) :
    rows_STR.circle.fibre c ⊆ rows_STR.edge.wholeVertical C ↔ phiVert_STR c = 0 := by
  have hn := norm_q_sq_STR c
  have hb := mem_cbase_STR.1 hc
  have hr := re_q_STR c
  simp only [phiVert_STR, gVert_STR]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := fibre_nonempty_STR c
    have h1 := ((mem_wholeVertical_STR C).1 (h hx)).2
    rw [fibre_height_STR c x hx] at h1
    linarith
  · intro h x hx
    rw [mem_wholeVertical_STR]
    have hu : uW_STR x ≤ 4 / 5 := by
      rw [fibre_re_STR c x hx, hr]
      have := hb.2.2
      simp only [phiBall_STR, gBall_STR] at this
      linarith
    refine ⟨hu, ?_⟩
    rw [fibre_height_STR c x hx]
    linarith

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
