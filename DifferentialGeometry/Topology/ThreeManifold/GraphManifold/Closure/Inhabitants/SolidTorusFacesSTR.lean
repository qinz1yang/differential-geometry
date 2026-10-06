import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusFaceSetsSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusFrontierSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G6: the face facts of the junctions

`faces_STR : JunctionFaceFacts74 A D rows_STR` for the solid torus cut. The horizontal map sends
both endpoints `t = 0, 1` of the edge base to the ball face (`ballRes_STR`); the whole end disks
lie in `{u = κ}` and together make `hdisk = {u = κ, h ≤ -7/8}` (`horizontalDisks_STR`,
`t_zero_or_one_iff_STR`); `P ∩ F` is `hdisk` for the ball face and empty for the cusp face; the
frontier of `M₂` is `∂M₂` (`frontier_M2_STR`); `M₃ ∩ ∂M₂` is `∂M₂` minus the relative interior of
`hdisk`, which is `{u = κ, h < -7/8}` (`frequently_sphere_above_level_STR`); there are no slim
ends, so the two slim clauses are vacuous.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_FacesSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_FacesSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

/-! ## The end disks -/

/-- The union of the two end disks: `{u = κ, h ≤ -7/8}`. -/
def hdisk_STR : Set Wc.Carrier :=
  {p | uW_STR p = 4 / 5 ∧ X135Radial.height p ≤ -(7 / 8 : ℝ)}

theorem mem_edgeParent_of_STR {p : Wc.Carrier} (hu : uW_STR p ≤ 4 / 5)
    (hh : X135Radial.height p ≤ -(7 / 8 : ℝ)) : p ∈ edgeParent_STR := by
  have hs : ‖sphereFirst p.val‖ ^ 2 ≤ 1 / 16 := by
    rw [height_eq_of_first_STR] at hh
    linarith
  have hn := norm_sphereFirst_sq_add p.val
  have hk : kap_STR < ‖sphereSecond p.val‖ := by
    have h0 := norm_nonneg (sphereSecond p.val)
    norm_num [kap_STR]
    nlinarith
  refine ⟨by linarith, ?_⟩
  have : (sphereSecond p.val).re ≤ 4 / 5 := hu
  change (sphereSecond p.val).re < ‖sphereSecond p.val‖
  norm_num [kap_STR] at hk
  linarith

theorem fibreSet_sub_hdisk_STR {τ : ℝ} (hτ : τ = 0 ∨ τ = 1) : fibreSet_STR τ ⊆ hdisk_STR := by
  rintro y ⟨hy, ht, hs⟩
  refine ⟨(t_zero_or_one_iff_STR hy).1 (by rw [ht]; exact hτ), ?_⟩
  rw [height_eq_of_first_STR]
  linarith

theorem hdisk_sub_fibreSet_STR {y : Wc.Carrier} (hy : y ∈ hdisk_STR) :
    ∃ τ : ℝ, (τ = 0 ∨ τ = 1) ∧ y ∈ fibreSet_STR τ := by
  have hp : y ∈ edgeParent_STR := mem_edgeParent_of_STR hy.1.le hy.2
  refine ⟨tOf_STR (sphereSecond y.val), (t_zero_or_one_iff_STR hp).2 hy.1, hp, rfl, ?_⟩
  have h := hy.2
  rw [height_eq_of_first_STR] at h
  linarith

/-- The coordinate `t` of a point of the edge base. -/
def coordE_STR (c : Base1_STR) : ℝ := (c.val : EuclideanSpace ℝ (Fin 1)) 0

theorem rows_disk_STR (c : rows_STR.edge.Base) :
    rows_STR.edge.disk c = fibreSet_STR (coordE_STR c) :=
  disk_eq_STR ballZeroDomainsL_STR c

theorem rows_residualSet_ball_STR :
    rows_STR.slimPieces.residualSet ballRes_STR = {p | uW_STR p = 4 / 5} :=
  residualSet_ball_STR

theorem rows_residualSet_cusp_STR :
    rows_STR.slimPieces.residualSet cuspRes_STR = {p | X135Radial.height p = -(1 / 4 : ℝ)} :=
  residualSet_cusp_STR

theorem edgeEnd_val_STR (e : rows_STR.edge.EdgeEnd) :
    coordE_STR e.1 = 0 ∨ coordE_STR e.1 = 1 := by
  have h : e.1 ∈ frontier (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR) := e.2
  rw [frontier_cbase_STR] at h
  exact h

/-- The endpoint of the edge base at `t = τ`, `τ ∈ {0, 1}`. -/
def endAt_STR (τ : ℝ) (hτ : τ = 0 ∨ τ = 1) : rows_STR.edge.EdgeEnd :=
  ⟨⟨EuclideanSpace.single (0 : Fin 1) τ, trivial⟩, by
    change (⟨EuclideanSpace.single (0 : Fin 1) τ, trivial⟩ : Base1_STR) ∈
      frontier (Subtype.val ⁻¹' edgeC2_STR : Set Base1_STR)
    rw [frontier_cbase_STR]
    simpa using hτ⟩

theorem horizontalDisks_STR : rows_STR.edge.horizontalDisks = hdisk_STR := by
  unfold EdgeBundle.horizontalDisks
  ext y
  constructor
  · intro hy
    obtain ⟨e, he⟩ := mem_iUnion.1 hy
    exact fibreSet_sub_hdisk_STR (edgeEnd_val_STR e) ((Set.ext_iff.1 (rows_disk_STR e.1) y).1 he)
  · intro hy
    obtain ⟨τ, hτ, hmem⟩ := hdisk_sub_fibreSet_STR hy
    refine mem_iUnion.2 ⟨endAt_STR τ hτ, ?_⟩
    refine (Set.ext_iff.1 (rows_disk_STR (endAt_STR τ hτ).1) y).2 ?_
    change y ∈ fibreSet_STR (EuclideanSpace.single (0 : Fin 1) τ 0)
    simpa using hmem

/-! ## The relative interior of the end disks in `∂M₂` -/

theorem relInt_hdisk_STR :
    relInt slimPieces_STR.boundaryM2 hdisk_STR =
      {p | p ∈ slimPieces_STR.boundaryM2 ∧ uW_STR p = 4 / 5 ∧
        X135Radial.height p < -(7 / 8 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxD' : x ∈ Subtype.val ⁻¹' hdisk_STR := interior_subset hx
    have hxD : x.val ∈ hdisk_STR := hxD'
    refine ⟨x.2, hxD.1, ?_⟩
    by_contra hlt
    have heq : X135Radial.height x.val = -(7 / 8 : ℝ) := le_antisymm hxD.2 (not_lt.mp hlt)
    have hfreq := frequently_sphere_above_level_STR hxD.1 heq
    obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype slimPieces_STR.boundaryM2 x _).1
      (isOpen_interior.mem_nhds hx)
    obtain ⟨y, ⟨hyu, hyh⟩, hyV⟩ := (hfreq.and_eventually hV).exists
    have hyA : y ∈ slimPieces_STR.boundaryM2 :=
      (Set.ext_iff.1 boundaryM2_eq_STR y).2 (Or.inl hyu)
    have h1 := interior_subset (hVsub (show (⟨y, hyA⟩ : slimPieces_STR.boundaryM2) ∈ _ from hyV))
    have h2 : X135Radial.height y ≤ -(7 / 8 : ℝ) := h1.2
    linarith
  · rintro ⟨hA, hu, hlt⟩
    refine ⟨⟨p, hA⟩, ?_, rfl⟩
    refine mem_interior.2 ⟨{x : slimPieces_STR.boundaryM2 |
      X135Radial.height x.val < -(7 / 8 : ℝ)}, ?_, ?_, hlt⟩
    · intro x hx
      have hxA : x.val ∈ ({p | uW_STR p = 4 / 5} ∪ {p | X135Radial.height p = -(1 / 4 : ℝ)} :
          Set Wc.Carrier) := (Set.ext_iff.1 boundaryM2_eq_STR x.val).1 x.2
      rcases hxA with hxu | hxc
      · exact ⟨hxu, hx.le⟩
      · exfalso
        have : X135Radial.height x.val = -(1 / 4 : ℝ) := hxc
        have hx' : X135Radial.height x.val < -(7 / 8 : ℝ) := hx
        linarith
    · exact isOpen_lt (X135Radial.height_continuous.comp continuous_subtype_val) continuous_const

/-! ## The face facts -/

/-- **The face facts of the junctions of the solid torus cut.** -/
def faces_STR : JunctionFaceFacts74 (stageGeometry_STR ballZeroDomainsL_STR)
    (cutChoice_STR ballZeroDomainsL_STR) rows_STR where
  horizontal _ := ballRes_STR
  horizontal_disk e := by
    intro y hy
    have h1 : y ∈ fibreSet_STR (coordE_STR e.1) := (Set.ext_iff.1 (rows_disk_STR e.1) y).1 hy
    exact (Set.ext_iff.1 rows_residualSet_ball_STR y).2
      (fibreSet_sub_hdisk_STR (edgeEnd_val_STR e) h1).1
  edge_faces F := by
    rcases res_cases_STR F with rfl | rfl
    · rw [rows_residualSet_ball_STR, edgeSet_eq_STR]
      ext p
      constructor
      · rintro ⟨⟨_, hh⟩, hu⟩
        have hp : p ∈ rows_STR.edge.horizontalDisks := by
          rw [horizontalDisks_STR]
          exact ⟨hu, hh⟩
        obtain ⟨e, he⟩ := mem_iUnion.1 hp
        exact mem_iUnion.2 ⟨e, mem_iUnion.2 ⟨rfl, he⟩⟩
      · intro hp
        obtain ⟨e, hp⟩ := mem_iUnion.1 hp
        obtain ⟨-, hp⟩ := mem_iUnion.1 hp
        have hq : p ∈ rows_STR.edge.horizontalDisks := mem_iUnion.2 ⟨e, hp⟩
        rw [horizontalDisks_STR] at hq
        exact ⟨⟨hq.1.le, hq.2⟩, hq.1⟩
    · rw [rows_residualSet_cusp_STR, edgeSet_eq_STR]
      ext p
      constructor
      · rintro ⟨⟨_, h3⟩, h2⟩
        have h2' : X135Radial.height p = -(1 / 4 : ℝ) := h2
        have h3' : X135Radial.height p ≤ -(7 / 8 : ℝ) := h3
        linarith
      · intro hp
        obtain ⟨e, hp⟩ := mem_iUnion.1 hp
        obtain ⟨h, -⟩ := mem_iUnion.1 hp
        exact (ballRes_ne_cuspRes_STR h).elim
  frontier_M2 := frontier_M2_STR.trans boundaryM2_eq_STR.symm
  region_boundary := by
    change (cutChoice_STR ballZeroDomainsL_STR).M₃ ∩ slimPieces_STR.boundaryM2 =
      slimPieces_STR.boundaryM2 \ relInt slimPieces_STR.boundaryM2
        rows_STR.edge.horizontalDisks
    rw [M3_eq_STR, horizontalDisks_STR, relInt_hdisk_STR]
    ext p
    constructor
    · rintro ⟨⟨hu, h1, h2⟩, hbd⟩
      exact ⟨hbd, fun hn => absurd h1 (not_le.2 hn.2.2)⟩
    · rintro ⟨hbd, hn⟩
      have hbd' : p ∈ ({p | uW_STR p = 4 / 5} ∪ {p | X135Radial.height p = -(1 / 4 : ℝ)} :
          Set Wc.Carrier) := (Set.ext_iff.1 boundaryM2_eq_STR p).1 hbd
      refine ⟨?_, hbd⟩
      rcases hbd' with hu | hc
      · have hh : X135Radial.height p < -(1 / 4 : ℝ) := height_lt_of_uW_STR hu
        refine ⟨hu.le, ?_, hh.le⟩
        by_contra hlt
        exact hn ⟨hbd, hu, not_le.1 hlt⟩
      · have hu : uW_STR p < 4 / 5 := uW_lt_kap_of_height_STR hc
        have hh : X135Radial.height p = -(1 / 4 : ℝ) := hc
        exact ⟨hu.le, by rw [hh]; norm_num, hh.le⟩
  slim_M2 := by
    rw [slimSet_eq_STR]
    refine (empty_inter _).trans ?_
    symm
    refine eq_empty_of_forall_notMem fun p hp => ?_
    obtain ⟨e, -⟩ := mem_iUnion.1 hp
    exact end_false_STR e.1
  shared_removed σ := (end_false_STR σ.1).elim

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
