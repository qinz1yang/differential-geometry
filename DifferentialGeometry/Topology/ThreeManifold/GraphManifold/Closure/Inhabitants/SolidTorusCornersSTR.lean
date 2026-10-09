import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCornerNbhdSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7b: the corner facts

`corners_STR : CornerCutFacts74 faces_STR rims_STR`: for each of the two endpoints `t = 0, 1`, the
descent patch (`descent_STR`: `Tb = 15/16 - ‖q‖²`, `hb = ratioP q`), and, through the local kit
`exists_cornerRank_descended_of_local_JN74`, the rank and the descended face equation
`b(t) = 4 t (1 - t)` (`b' = ±4`) on the neighbourhood `proj⁻¹(patch)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_CornersSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CornersSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

theorem rimBase_mem_patch_STR (e : rows_STR.edge.EdgeEnd) : rims_STR.rimBase e.1 ∈ patch_STR := by
  have hτ := edgeEnd_val_STR e
  have hn := norm_q_sq_STR (rimBase_STR e.1)
  have hr := re_q_STR (rimBase_STR e.1)
  have hq := qOfBase_rimBase_STR e.1
  refine ⟨?_, ?_⟩
  · change 9 / 10 < ‖vOf_STR (rimBase_STR e.1)‖ ^ 2
    rw [← hn, hq, norm_sq_qRim_STR]
    norm_num
  · change |reL_STR (vOf_STR (rimBase_STR e.1)) - 4 / 5| < 1 / 100
    rw [← hr, hq, re_qRim_STR hτ]
    norm_num

theorem edgeProj_coord_STR (p : Wc.Carrier) (hx : p ∈ rows_STR.edge.source) :
    coordE_STR (rows_STR.edge.proj ⟨p, hx⟩) = tOf_STR (sphereSecond p.val) :=
  edgeProj_val_STR ⟨p, (stageGeometry_STR ballZeroDomainsL_STR).edge.restrictParent_le _ hx⟩

theorem cornerT_eq_STR (x : rows_STR.circle.domain) (hx : x ∈ nbhd_STR) :
    rows_STR.cornerT x = ‖sphereFirst x.val.val‖ ^ 2 - 1 / 16 := by
  have hxS := nbhd_edgeSource_STR x hx
  simp only [StageCutRows74.cornerT, hxS, ↓reduceDIte]
  rfl

/-- **The descent data of an endpoint.** -/
def descent_STR (e : rows_STR.edge.EdgeEnd) : CornerDescent74 faces_STR rims_STR e where
  patch := patch_STR
  rim_mem := rimBase_mem_patch_STR e
  Tb := fun c => 15 / 16 - ‖vOf_STR c‖ ^ 2
  hb := fun c => ratioP_STR (qOfBase_STR c.1)
  Tb_smooth := (contMDiff_phi_STR (g := fun z : EuclideanSpace ℝ (Fin 2) => 15 / 16 - ‖z‖ ^ 2)
    (contDiff_const.sub (contDiff_norm_sq ℝ))).contMDiffOn
  hb_smooth := (contMDiff_phi_STR (g := fun z : EuclideanSpace ℝ (Fin 2) =>
    ratioP_STR (modelPlaneComplex z))
    (contDiff_ratioP_STR.comp modelPlaneComplex.contDiff)).contMDiffOn
  desc x hx := by
    have hxn : x ∈ nbhd_STR := hx
    refine ⟨?_, ?_⟩
    · rw [cornerT_eq_STR x hxn]
      have hn := norm_sphereFirst_sq_add x.val.val
      have h2 := second_proj_STR x
      have h3 := norm_q_sq_STR (rows_STR.circle.proj x)
      rw [h2] at hn
      linarith
    · change ratioP_STR (sphereSecond x.val.val) =
        ratioP_STR (qOfBase_STR (rows_STR.circle.proj x).1)
      rw [second_proj_STR x]
  center := by
    have hτ := edgeEnd_val_STR e
    have hn := norm_q_sq_STR (rimBase_STR e.1)
    have hq := qOfBase_rimBase_STR e.1
    refine ⟨?_, ?_⟩
    · change 15 / 16 - ‖vOf_STR (rimBase_STR e.1)‖ ^ 2 = 0
      rw [← hn, hq, norm_sq_qRim_STR]
      norm_num
    · change ratioP_STR (qOfBase_STR (rimBase_STR e.1).1) = 0
      rw [hq, ratioP_STR, re_qRim_STR hτ]
      norm_num [kap_STR]

theorem component_val_STR (C : rows_STR.edge.EdgeBaseComponent) :
    C.1 = (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := by
  rw [actualComponent_eq_STR C]
  exact cbaseComp_val_STR

/-- **The rank and the descended equation of an endpoint** (local kit
`exists_cornerRank_descended_of_local_JN74`, `b = 4 t (1 - t)` on `proj⁻¹(patch)`). -/
theorem cornerExists_STR (e : rows_STR.edge.EdgeEnd) :
    ∃ K : CornerRank74 faces_STR rims_STR e, Nonempty (CornerDescended74 K) := by
  have hfib : ∃ p : rows_STR.circle.domain, rows_STR.circle.proj p = rims_STR.rimBase e.1 := by
    obtain ⟨x, y, hy, -⟩ := fibre_nonempty_STR (rimBase_STR e.1)
    exact ⟨y, hy⟩
  refine exists_cornerRank_descended_of_local_JN74 (F := faces_STR) (G := rims_STR) e
    (descent_STR e) hfib bE_STR ⊤ trivial contMDiff_bE_STR.contMDiffOn (mfderiv_bE_ne_STR e)
    nbhd_STR nbhd_open_STR ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h : rows_STR.circle.proj p = rims_STR.rimBase e.1 := hp
    change rows_STR.circle.proj p ∈ (patch_STR : Set rows_STR.circle.Base)
    rw [h]
    exact rimBase_mem_patch_STR e
  · intro x hx
    refine ⟨nbhd_edgeSource_STR x hx, ?_⟩
    change X135Radial.height x.val < 0
    linarith [nbhd_height_STR x hx]
  · intro x hx
    have hxS := nbhd_edgeSource_STR x hx
    refine ⟨hxS, ?_⟩
    change ratioL_STR x.val = bE_STR (rows_STR.edge.proj ⟨x.val, hxS⟩)
    rw [ratioL_eq_b_STR x hx, bE_STR, edgeProj_coord_STR x.val hxS]
  · intro x hx
    rw [M2_eq_STR]
    change (uW_STR x.val ≤ 4 / 5 ∧ X135Radial.height x.val ≤ -(1 / 4 : ℝ)) ↔
      0 ≤ lamMix_STR (sphereSecond x.val.val) * ((4 / 5 : ℝ) - (sphereSecond x.val.val).re)
    have hh := nbhd_height_STR x hx
    have hΛ := lamMix_pos_STR (sphereSecond x.val.val)
    rw [mul_nonneg_iff_of_pos_left hΛ]
    have hu : uW_STR x.val = (sphereSecond x.val.val).re := rfl
    rw [hu]
    constructor
    · rintro ⟨h, -⟩
      linarith
    · intro h
      exact ⟨by linarith, by linarith⟩
  · intro x hx
    rw [edgeSet_eq_STR]
    change (uW_STR x.val ≤ 4 / 5 ∧ X135Radial.height x.val ≤ -(7 / 8 : ℝ)) ↔
      0 ≤ lamMix_STR (sphereSecond x.val.val) * ((4 / 5 : ℝ) - (sphereSecond x.val.val).re) ∧
        rows_STR.cornerT x ≤ 0
    have hΛ := lamMix_pos_STR (sphereSecond x.val.val)
    rw [mul_nonneg_iff_of_pos_left hΛ, cornerT_eq_STR x hx]
    have hu : uW_STR x.val = (sphereSecond x.val.val).re := rfl
    have hh := height_eq_of_first_STR x.val
    rw [hu]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  · intro x hx hxS
    rw [component_val_STR e.component]
    change (0 ≤ coordE_STR (rows_STR.edge.proj ⟨x.val, hxS⟩) ∧
      coordE_STR (rows_STR.edge.proj ⟨x.val, hxS⟩) ≤ 1) ↔
        0 ≤ bE_STR (rows_STR.edge.proj ⟨x.val, hxS⟩)
    rw [bE_STR]
    generalize coordE_STR (rows_STR.edge.proj ⟨x.val, hxS⟩) = t
    constructor
    · rintro ⟨h0, h1⟩
      have := mul_nonneg h0 (sub_nonneg.2 h1)
      linarith
    · intro h
      constructor
      · by_contra hcon
        nlinarith [not_le.1 hcon]
      · by_contra hcon
        nlinarith [not_le.1 hcon]

/-- **`CornerCutFacts74`** of the solid torus cut: both endpoints `t = 0, 1`. -/
def corners_STR : CornerCutFacts74 faces_STR rims_STR where
  descent e := descent_STR e
  rank e := Classical.choose (cornerExists_STR e)
  descended e := Classical.choice (Classical.choose_spec (cornerExists_STR e))

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
