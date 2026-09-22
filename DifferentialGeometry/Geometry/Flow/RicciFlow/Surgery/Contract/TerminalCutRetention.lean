import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCoreTruncation
import DifferentialGeometry.Geometry.Neck.ScalarRetainedCore

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology



namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem retainedCore_subset_terminal_of_slices_removed
    {ι : Type*} {δ : ι → ℝ}
    (f : ∀ i, bufferedCylinder (δ i) → D.stage.Carrier)
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e)
    (hcut : ∀ c ∈ P.component, ∀ e : P.hornIndex c, ∀ y : Sphere 2,
      (P.horn c e (y, t c e)).val ∈ ⋃ i, removedSlab (f i)) :
    MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
      (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
        (P.coreRadius ^ 2)⁻¹)) D.slab.terminalRegularOpen := by
  let K := (Subtype.val : D.slab.terminalRegularOpen → D.stage.Carrier) '' P.truncatedRegion t
  have hlow : ∀ x : D.slab.terminalRegularOpen,
      metricScalarAt D.terminal.metric x ≤ (P.coreRadius ^ 2)⁻¹ → x.val ∈ K := by
    intro x hx
    exact ⟨x, P.low_subset_truncatedRegion t hx, rfl⟩
  have hfront : frontier K ⊆ ⋃ i, removedSlab (f i) := by
    intro x hx
    obtain ⟨c, hc, e, y, hxy⟩ := by
      simpa only [mem_iUnion, mem_range] using P.ambient_truncatedRegion_frontier_subset_slices t
        ht hx
    exact hxy ▸ hcut c hc e y
  have hsub := scalarSublevelComponents_retained_subset_of_frontier_removed
    D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius ^ 2)⁻¹ K hlow hfront
  intro p hp
  obtain ⟨x, _, hx⟩ := interior_subset (hsub ⟨p, hp, rfl⟩)
  exact hx ▸ x.property


theorem retainedCore_subset_terminal_of_neck_slices
    {ι : Type*} {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i)
    (f : ∀ i, bufferedCylinder (δ i) → D.stage.Carrier)
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e)
    (index : ∀ c, P.hornIndex c → ι)
    (hneck : ∀ c ∈ P.component, ∀ e : P.hornIndex c, ∀ y : Sphere 2,
      f (index c e) ⟨(y, 0), by
        change -(δ (index c e))⁻¹ - 1 < 0 ∧ 0 < (δ (index c e))⁻¹ + 1
        constructor <;> linarith [inv_pos.mpr (hδ (index c e))]⟩ =
        (P.horn c e (y, t c e)).val) :
    MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
      (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
        (P.coreRadius ^ 2)⁻¹)) D.slab.terminalRegularOpen := by
  apply P.retainedCore_subset_terminal_of_slices_removed f t ht
  intro c hc e y
  refine mem_iUnion.mpr ⟨index c e, ?_⟩
  refine ⟨⟨(y, 0), ?_⟩, ?_, hneck c hc e y⟩
  · change -(δ (index c e))⁻¹ - 1 < 0 ∧ 0 < (δ (index c e))⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr (hδ (index c e))]
  · change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
    norm_num

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

abbrev HornCutIndex := Σ c : P.component, P.hornIndex c.val

def hornCutMap (δ : P.HornCutIndex → ℝ) (t : ∀ c, P.hornIndex c → ℝ)
    (j : P.HornCutIndex) : bufferedCylinder (δ j) → D.stage.Carrier :=
  fun q => (P.horn j.1.val j.2 (q.val.1, t j.1.val j.2 - q.val.2)).val

theorem horn_mem_component (c : ConnectedComponents D.slab.terminalRegularOpen)
    (hc : c ∈ P.component) (e : P.hornIndex c) (y : Sphere 2) {a : ℝ} (ha : 0 ≤ a) :
    ConnectedComponents.mk (P.horn c e (y, a)) = c := by
  have hmem : P.horn c e (y, a) ∈
      P.core c ∪ ⋃ e, range (fun p : HalfNeckCylinder => P.horn c e p.val) :=
    Or.inr (mem_iUnion.mpr ⟨e, ⟨⟨(y, a), ha⟩, rfl⟩⟩)
  rw [← P.horn_covers_component c hc] at hmem
  exact hmem

theorem core_subset_cutCore_hornCutMap
    (δ : P.HornCutIndex → ℝ) (t : ∀ c, P.hornIndex c → ℝ)
    (ht : ∀ c e, 1 < t c e)
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component) :
    (Subtype.val : D.slab.terminalRegularOpen → D.stage.Carrier) '' P.core c ⊆
      cutCore (P.hornCutMap δ t) := by
  rintro x ⟨x, hx, rfl⟩ hcut
  obtain ⟨j, q, hq, heq⟩ := mem_iUnion.mp hcut
  have hu : 0 < t j.1.val j.2 - q.val.2 := by
    change -1 < q.val.2 ∧ q.val.2 < 1 at hq
    linarith [ht j.1.val j.2, hq.2]
  have hpoint : P.horn j.1.val j.2 (q.val.1, t j.1.val j.2 - q.val.2) = x :=
    Subtype.ext heq
  have hjc : j.1.val = c := by
    have hcomp := P.horn_mem_component j.1.val j.1.property j.2 q.val.1 hu.le
    rw [hpoint] at hcomp
    exact hcomp.symm.trans (P.core_subset_component c hc hx)
  have hxj : x ∈ P.core j.1.val := hjc.symm ▸ hx
  exact P.horn_pos_notMem_core j.1.val j.2 q.val.1 hu (hpoint.symm ▸ hxj)

theorem horn_segment_subset_cutCore_hornCutMap
    (δ : P.HornCutIndex → ℝ) (t : ∀ c, P.hornIndex c → ℝ)
    (ht : ∀ c e, 1 < t c e) (j : P.HornCutIndex) :
    (fun x : D.slab.terminalRegularOpen => x.val) ''
      (P.horn j.1.val j.2 '' (univ ×ˢ Icc (0 : ℝ) (t j.1.val j.2 - 1))) ⊆
        cutCore (P.hornCutMap δ t) := by
  rintro x ⟨_, ⟨p, hp, rfl⟩, rfl⟩ hcut
  obtain ⟨k, q, hq, heq⟩ := mem_iUnion.mp hcut
  have hu : 0 < t k.1.val k.2 - q.val.2 := by
    change -1 < q.val.2 ∧ q.val.2 < 1 at hq
    linarith [ht k.1.val k.2, hq.2]
  have hpoint : P.horn k.1.val k.2 (q.val.1, t k.1.val k.2 - q.val.2) =
      P.horn j.1.val j.2 p := Subtype.ext heq
  have hcomp : k.1.val = j.1.val := by
    have hk := P.horn_mem_component k.1.val k.1.property k.2 q.val.1 hu.le
    have hj := P.horn_mem_component j.1.val j.1.property j.2 p.1 hp.2.1
    rw [hpoint] at hk
    exact hk.symm.trans hj
  have hbase : k.1 = j.1 := Subtype.ext hcomp
  rcases j with ⟨jc, je⟩
  rcases k with ⟨kc, ke⟩
  dsimp only at hbase hpoint hp hu hq
  subst kc
  have hke : ke = je := by
    by_contra hne
    exact Set.disjoint_left.mp (P.horn_range_disjoint jc.val ke je hne)
      ⟨⟨(q.val.1, t jc.val ke - q.val.2), hu.le⟩, hpoint⟩
      ⟨⟨p, hp.2.1⟩, rfl⟩
  subst ke
  have hcoords := P.horn_injOn jc.val je (show (q.val.1, t jc.val je - q.val.2) ∈ univ ×ˢ Ici (0 :
    ℝ) from ⟨mem_univ _, hu.le⟩)
    (show p ∈ univ ×ˢ Ici (0 : ℝ) from ⟨hp.1, hp.2.1⟩) hpoint
  have hz := congrArg Prod.snd hcoords
  change t jc.val je - q.val.2 = p.2 at hz
  change -1 < q.val.2 ∧ q.val.2 < 1 at hq
  linarith [hp.2.2, hq.2]


theorem inner_horn_point_mem_retainedCore
    (δ : P.HornCutIndex → ℝ) (t : ∀ c, P.hornIndex c → ℝ)
    (ht : ∀ c e, 1 < t c e) (j : P.HornCutIndex) (y : Sphere 2) :
    ∃ hx : (P.horn j.1.val j.2 (y, t j.1.val j.2 - 1)).val ∈ cutCore (P.hornCutMap δ t),
      (⟨(P.horn j.1.val j.2 (y, t j.1.val j.2 - 1)).val, hx⟩ : cutCore (P.hornCutMap δ t)) ∈
        retainedCore (P.hornCutMap δ t)
          (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ t)
            (P.coreRadius ^ 2)⁻¹) := by
  let U := D.slab.terminalRegularOpen
  let core := cutCore (P.hornCutMap δ t)
  let S := P.core j.1.val ∪ P.horn j.1.val j.2 '' (univ ×ˢ Icc (0 : ℝ) (t j.1.val j.2 - 1))
  have hs : IsPreconnected S := by
    have hsphere : IsPreconnected (univ : Set (Sphere 2)) := by
      let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
        (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
          (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
      exact isPreconnected_univ
    have hprod := hsphere.prod (isPreconnected_Icc : IsPreconnected (Icc (0 : ℝ) (t j.1.val j.2 -
      1)))
    have himage : IsPreconnected (P.horn j.1.val j.2 '' (univ ×ˢ Icc (0 : ℝ) (t j.1.val j.2 - 1)))
      :=
      hprod.image _ ((P.horn_smooth j.1.val j.2).continuousOn.mono (fun p hp => ⟨hp.1, hp.2.1⟩))
    exact IsPreconnected.union (P.horn j.1.val j.2 (y, 0))
      (P.horn_base_mem_core j.1.val j.2 y)
      ⟨(y, 0), ⟨mem_univ _, le_rfl, by linarith [ht j.1.val j.2]⟩, rfl⟩
      (P.core_isConnected j.1.val j.1.property).isPreconnected himage
  have hsub : ∀ x : S, (x.val : U).val ∈ core := by
    intro x
    rcases x.property with hx | hx
    · exact P.core_subset_cutCore_hornCutMap δ t ht j.1.val j.1.property ⟨x.val, hx, rfl⟩
    · exact P.horn_segment_subset_cutCore_hornCutMap δ t ht j ⟨x.val, hx, rfl⟩
  let F : S → core := fun x => ⟨x.val.val, hsub x⟩
  have hF : Continuous F := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hs
  have hconstant (x z : S) : ConnectedComponents.mk (F x) = ConnectedComponents.mk (F z) := by
    apply ConnectedComponents.coe_eq_coe'.mpr
    have himg : IsPreconnected (F '' (univ : Set S)) := isPreconnected_univ.image F hF.continuousOn
    exact himg.subset_connectedComponent ⟨z, mem_univ _, rfl⟩ ⟨x, mem_univ _, rfl⟩
  obtain ⟨x, hxc, hxlow⟩ := (P.component_iff_meets_low j.1.val).mp j.1.property
  have hxcore : x ∈ P.core j.1.val := interior_subset (P.low_mem_interior_core j.1.val j.1.property
    x hxc hxlow)
  let q : S := ⟨P.horn j.1.val j.2 (y, t j.1.val j.2 - 1),
    Or.inr ⟨(y, t j.1.val j.2 - 1), ⟨mem_univ _, by linarith [ht j.1.val j.2], le_rfl⟩, rfl⟩⟩
  let p : S := ⟨x, Or.inl hxcore⟩
  refine ⟨hsub q, x, hxlow, hsub p, ?_⟩
  exact hconstant p q


theorem hornIndex_component_mem (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) : c ∈ P.component := by
  by_contra hc
  exact (P.hornIndex_empty c hc).false e

theorem hornCutMap_slices_removed
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j)
    (t : ∀ c, P.hornIndex c → ℝ) :
    ∀ c ∈ P.component, ∀ e : P.hornIndex c, ∀ y : Sphere 2,
      (P.horn c e (y, t c e)).val ∈ ⋃ j, removedSlab (P.hornCutMap δ t j) := by
  intro c hc e y
  let j : P.HornCutIndex := ⟨⟨c, hc⟩, e⟩
  refine mem_iUnion.mpr ⟨j, ?_⟩
  refine ⟨⟨(y, 0), ?_⟩, ?_, ?_⟩
  · change -(δ j)⁻¹ - 1 < 0 ∧ 0 < (δ j)⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr (hδ j)]
  · change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
    norm_num
  · change (P.horn c e (y, t c e - 0)).val = _
    rw [sub_zero]

theorem hornCutMap_retained_terminal
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j)
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e) :
    MapsTo (Subtype.val : cutCore (P.hornCutMap δ t) → D.stage.Carrier)
      (retainedCore (P.hornCutMap δ t)
        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ t)
          (P.coreRadius ^ 2)⁻¹)) D.slab.terminalRegularOpen :=
  P.retainedCore_subset_terminal_of_slices_removed (P.hornCutMap δ t) t ht
    (P.hornCutMap_slices_removed δ hδ t)

theorem outer_horn_point_not_mem_truncatedRegion
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e)
    (j : P.HornCutIndex) (y : Sphere 2) :
    P.horn j.1.val j.2 (y, t j.1.val j.2 + 1) ∉ P.truncatedRegion t := by
  intro hx
  obtain ⟨c, hc, hxC⟩ := mem_iUnion₂.mp hx
  have hcj : c = j.1.val := by
    exact (P.truncatedCore_subset_component c hc (t c) hxC).symm.trans
      (P.horn_mem_component j.1.val j.1.property j.2 y (by linarith [ht j.1.val j.2]))
  subst c
  have hxT : P.horn j.1.val j.2 (y, t j.1.val j.2 + 1) ∈ P.hornTail j.1.val j.2 (t j.1.val j.2) :=
    ⟨(y, t j.1.val j.2 + 1), ⟨mem_univ _, by change t j.1.val j.2 ≤ t j.1.val j.2 + 1; linarith⟩,
      rfl⟩
  obtain ⟨z, hz⟩ := P.truncatedCore_inter_tail_subset_slice j.1.val (t j.1.val) (ht j.1.val) j.2
    ⟨hxC, hxT⟩
  have hcoord := P.horn_injOn j.1.val j.2
    (show (z, t j.1.val j.2) ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _, (ht _ _).le⟩)
    (show (y, t j.1.val j.2 + 1) ∈ univ ×ˢ Ici (0 : ℝ) from
      ⟨mem_univ _, by
        change 0 ≤ t j.1.val j.2 + 1; linarith [ht j.1.val j.2]⟩) hz
  have hbad := congrArg Prod.snd hcoord
  linarith

theorem outer_horn_point_not_mem_retainedCore
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j)
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e)
    (j : P.HornCutIndex) (y : Sphere 2)
    (hx : (P.horn j.1.val j.2 (y, t j.1.val j.2 + 1)).val ∈ cutCore (P.hornCutMap δ t)) :
    (⟨(P.horn j.1.val j.2 (y, t j.1.val j.2 + 1)).val, hx⟩ : cutCore (P.hornCutMap δ t)) ∉
      retainedCore (P.hornCutMap δ t)
        (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ t)
          (P.coreRadius ^ 2)⁻¹) := by
  intro hret
  let K := (Subtype.val : D.slab.terminalRegularOpen → D.stage.Carrier) '' P.truncatedRegion t
  have hfront : frontier K ⊆ ⋃ i, removedSlab (P.hornCutMap δ t i) := by
    intro x hxf
    obtain ⟨c, hc, e, y, hxy⟩ := by
      simpa only [mem_iUnion, mem_range] using P.ambient_truncatedRegion_frontier_subset_slices t
        ht hxf
    exact hxy ▸ P.hornCutMap_slices_removed δ hδ t c hc e y
  have hsub := scalarSublevelComponents_retained_subset_of_frontier_removed
    D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ t) (P.coreRadius ^ 2)⁻¹ K
    (fun x hx => ⟨x, P.low_subset_truncatedRegion t hx, rfl⟩) hfront
  obtain ⟨x, hxK, heq⟩ := interior_subset (hsub ⟨_, hret, rfl⟩)
  have hxx : x = P.horn j.1.val j.2 (y, t j.1.val j.2 + 1) := Subtype.ext heq
  exact P.outer_horn_point_not_mem_truncatedRegion t ht j y (hxx ▸ hxK)


theorem outer_horn_point_mem_cutCore
    (δ : P.HornCutIndex → ℝ) (t : ∀ c, P.hornIndex c → ℝ)
    (ht : ∀ c e, 1 < t c e) (j : P.HornCutIndex) (y : Sphere 2) :
    (P.horn j.1.val j.2 (y, t j.1.val j.2 + 1)).val ∈ cutCore (P.hornCutMap δ t) := by
  intro hcut
  obtain ⟨k, q, hq, heq⟩ := mem_iUnion.mp hcut
  have hu : 0 < t k.1.val k.2 - q.val.2 := by
    change -1 < q.val.2 ∧ q.val.2 < 1 at hq
    linarith [ht k.1.val k.2, hq.2]
  have hp : 0 ≤ t j.1.val j.2 + 1 := by linarith [ht j.1.val j.2]
  have hpoint : P.horn k.1.val k.2 (q.val.1, t k.1.val k.2 - q.val.2) =
      P.horn j.1.val j.2 (y, t j.1.val j.2 + 1) := Subtype.ext heq
  have hcomp : k.1.val = j.1.val := by
    have hk := P.horn_mem_component k.1.val k.1.property k.2 q.val.1 hu.le
    have hj := P.horn_mem_component j.1.val j.1.property j.2 y hp
    rw [hpoint] at hk
    exact hk.symm.trans hj
  have hbase : k.1 = j.1 := Subtype.ext hcomp
  rcases j with ⟨jc, je⟩
  rcases k with ⟨kc, ke⟩
  dsimp only at hbase hpoint hp hu hq
  subst kc
  have hke : ke = je := by
    by_contra hne
    exact Set.disjoint_left.mp (P.horn_range_disjoint jc.val ke je hne)
      ⟨⟨(q.val.1, t jc.val ke - q.val.2), hu.le⟩, hpoint⟩
      ⟨⟨(y, t jc.val je + 1), hp⟩, rfl⟩
  subst ke
  have hcoords := P.horn_injOn jc.val je
    (show (q.val.1, t jc.val je - q.val.2) ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _, hu.le⟩)
    (show (y, t jc.val je + 1) ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _, hp⟩) hpoint
  have hz := congrArg Prod.snd hcoords
  change t jc.val je - q.val.2 = t jc.val je + 1 at hz
  change -1 < q.val.2 ∧ q.val.2 < 1 at hq
  linarith [hq.1]

theorem hornCutMap_retains_exactly_inner_side
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j)
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 1 < t c e)
    (j : P.HornCutIndex) :
    (∀ y : Sphere 2,
      ∃ hx : (P.horn j.1.val j.2 (y, t j.1.val j.2 - 1)).val ∈ cutCore (P.hornCutMap δ t),
        (⟨(P.horn j.1.val j.2 (y, t j.1.val j.2 - 1)).val, hx⟩ : cutCore (P.hornCutMap δ t)) ∈
          retainedCore (P.hornCutMap δ t)
            (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ
              t)
              (P.coreRadius ^ 2)⁻¹)) ∧
    (∀ y : Sphere 2,
      ∃ hx : (P.horn j.1.val j.2 (y, t j.1.val j.2 + 1)).val ∈ cutCore (P.hornCutMap δ t),
        (⟨(P.horn j.1.val j.2 (y, t j.1.val j.2 + 1)).val, hx⟩ : cutCore (P.hornCutMap δ t)) ∉
          retainedCore (P.hornCutMap δ t)
            (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ
              t)
              (P.coreRadius ^ 2)⁻¹)) := by
  refine ⟨P.inner_horn_point_mem_retainedCore δ t ht j, ?_⟩
  intro y
  exact ⟨P.outer_horn_point_mem_cutCore δ t ht j y,
    P.outer_horn_point_not_mem_retainedCore δ hδ t (fun c e => lt_trans zero_lt_one (ht c e))
      j y _⟩


private local instance : Finite P.HornCutIndex := by
  let := P.component_finite.fintype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance

theorem hornCutMap_cuttingSphereComponent_mem_iff
    (δ : P.HornCutIndex → ℝ) (hδ : ∀ j, 0 < δ j)
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 1 < t c e)
    (hf : ∀ j, _root_.Topology.IsOpenEmbedding (P.hornCutMap δ t j))
    (hdisj : Pairwise fun j k => Disjoint (range (P.hornCutMap δ t j)) (range (P.hornCutMap δ t k)))
    (j : P.HornCutIndex) (side : Bool) :
    cuttingSphereComponent hδ (P.hornCutMap δ t) hf hdisj (j, side) ∈
      scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ t)
        (P.coreRadius ^ 2)⁻¹ ↔ side = true := by
  cases side
  · obtain ⟨hx, hn⟩ := (P.hornCutMap_retains_exactly_inner_side δ hδ t ht j).2 spherePoint
    have heq : cuttingSphereAttachment hδ (P.hornCutMap δ t) (fun j => (hf j).injective) hdisj
        ⟨(j, false), spherePoint⟩ =
        (⟨(P.horn j.1.val j.2 (spherePoint, t j.1.val j.2 + 1)).val, hx⟩ : cutCore (P.hornCutMap δ
          t)) := by
      apply Subtype.ext
      change (P.horn j.1.val j.2 (spherePoint, t j.1.val j.2 - (-1))).val = _
      rw [sub_neg_eq_add]
    change ConnectedComponents.mk _ ∈ _ ↔ false = true
    rw [heq]
    exact iff_of_false hn (by decide)
  · obtain ⟨hx, hm⟩ := (P.hornCutMap_retains_exactly_inner_side δ hδ t ht j).1 spherePoint
    have heq : cuttingSphereAttachment hδ (P.hornCutMap δ t) (fun j => (hf j).injective) hdisj
        ⟨(j, true), spherePoint⟩ =
        (⟨(P.horn j.1.val j.2 (spherePoint, t j.1.val j.2 - 1)).val, hx⟩ : cutCore (P.hornCutMap δ
          t)) := rfl
    change ConnectedComponents.mk _ ∈ _ ↔ true = true
    rw [heq]
    exact iff_of_true hm rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end

section

set_option autoImplicit false

open Set
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem exists_scalar_bound_hornCutMap_retained
    (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e) :
    ∃ K : ℝ, 0 < K ∧
      (∀ (j : P.HornCutIndex) (y : Sphere 2),
        metricScalarAt D.terminal.metric (P.horn j.1.val j.2 (y, t j.1.val j.2)) ≤ K) ∧
      ∀ δ : P.HornCutIndex → ℝ, (∀ j, 0 < δ j) →
        ∀ x : D.slab.terminalRegularOpen,
          (∃ hx : x.val ∈ cutCore (P.hornCutMap δ t),
            (⟨x.val, hx⟩ : cutCore (P.hornCutMap δ t)) ∈
              retainedCore (P.hornCutMap δ t)
                (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric
                  (P.hornCutMap δ t) (P.coreRadius ^ 2)⁻¹)) →
          metricScalarAt D.terminal.metric x ≤ K := by
  have hb := ((P.truncatedRegion_isCompact t).image
    (metricScalar_smooth D.terminal.metric).continuous).bddAbove
  obtain ⟨K₀, hK₀⟩ := hb
  let K := max K₀ 1
  have hbound : ∀ x ∈ P.truncatedRegion t, metricScalarAt D.terminal.metric x ≤ K := by
    intro x hx
    exact (hK₀ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  refine ⟨K, zero_lt_one.trans_le (le_max_right _ _), ?_, ?_⟩
  · intro j y
    exact hbound _ (mem_iUnion₂.mpr ⟨j.1.val, j.1.property,
      Or.inr (mem_iUnion.mpr ⟨j.2, (y, t j.1.val j.2),
        ⟨mem_univ _, (ht _ _).le, le_rfl⟩, rfl⟩)⟩)
  · intro δ hδ x hx
    let T := (Subtype.val : D.slab.terminalRegularOpen → D.stage.Carrier) '' P.truncatedRegion t
    have hfront : frontier T ⊆ ⋃ j, removedSlab (P.hornCutMap δ t j) := by
      intro z hz
      obtain ⟨c, hc, e, y, heq⟩ := by
        simpa only [mem_iUnion, mem_range] using
          P.ambient_truncatedRegion_frontier_subset_slices t ht hz
      exact heq ▸ P.hornCutMap_slices_removed δ hδ t c hc e y
    have hsub := scalarSublevelComponents_retained_subset_of_frontier_removed
      D.slab.terminalRegularOpen D.terminal.metric (P.hornCutMap δ t) (P.coreRadius ^ 2)⁻¹
      T (fun z hz => ⟨z, P.low_subset_truncatedRegion t hz, rfl⟩) hfront
    obtain ⟨hx, hret⟩ := hx
    obtain ⟨z, hz, heq⟩ := interior_subset (hsub ⟨⟨x.val, hx⟩, hret, rfl⟩)
    have hzx : z = x := Subtype.ext heq
    exact hzx ▸ hbound z hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end
