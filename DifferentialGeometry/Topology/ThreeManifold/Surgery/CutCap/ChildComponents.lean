import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.SmoothTransition
import DifferentialGeometry.Topology.ThreeManifold.Surgery.Capping.Cover
import DifferentialGeometry.Topology.Manifold.ImmersionImageNhds
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import Mathlib.Analysis.Convex.PathConnected

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem removedBand_isOpen (a : E.trace.tubes.Index) :
    IsOpen (E.trace.tubes.removedBand a) := by
  let : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z, hz, rfl⟩
  apply DifferentialGeometry.Topology.immersion_image_mem_nhds
    ((E.tube_smooth a).isImmersion.isImmersionAt z)
  · simp [ThreeSpace, Module.finrank_prod]
  · change z ∈ ((𝓡 2).prod (𝓡∂ 1)).interior TubeDomain
    rw [ModelWithCorners.interior_prod]
    exact ⟨BoundarylessManifold.isInteriorPoint,
      Icc_isInteriorPoint_interior ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  · exact ((isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)).mem_nhds hz

theorem core_compact : CompactSpace E.trace.tubes.core := by
  apply isCompact_iff_compactSpace.mp
  exact (isOpen_iUnion E.removedBand_isOpen).isClosed_compl.isCompact

theorem core_locallyConnected : LocallyConnectedSpace E.trace.tubes.core := by
  let := E.coreCharts
  exact ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) E.trace.tubes.core


def childCoreComponent (c : ConnectedComponents Q.Carrier) :
    ConnectedComponents E.trace.tubes.core :=
  letI := E.core_compact
  letI := E.core_locallyConnected
  E.trace.childCore c

def childParent (c : ConnectedComponents Q.Carrier) : ConnectedComponents P.Carrier :=
  letI := E.core_compact
  letI := E.core_locallyConnected
  E.trace.childParent c

abbrev ChildCore (c : ConnectedComponents Q.Carrier) :=
  ComponentCarrier (E.childCoreComponent c)

abbrev ParentCarrier (c : ConnectedComponents Q.Carrier) := ComponentCarrier (E.childParent c)

abbrev ChildCarrier (_E : SmoothCutCapTransition P Q D N)
    (c : ConnectedComponents Q.Carrier) := ComponentCarrier c

theorem childCore_mapsTo_child (c : ConnectedComponents Q.Carrier) (x : E.ChildCore c) :
    ∃! y : E.ChildCarrier c,
      E.trace.presentation (E.trace.capping.coreInclusion x.1) = Sum.inl y.1 := by
  classical
  let := E.core_compact
  let := E.core_locallyConnected
  obtain ⟨q, hq⟩ := ConnectedComponents.surjective_coe c
  have hcore : E.trace.capping.componentMap (E.childCoreComponent c) = E.trace.cappedChild c :=
    E.trace.capping.componentEquiv.apply_symm_apply _
  have hx := (congrArg E.trace.capping.componentMap x.2).trans hcore
  have hpres :
      ConnectedComponents.mk (E.trace.presentation (E.trace.capping.coreInclusion x.1)) =
        ConnectedComponents.mk (Sum.inl q : Q.Carrier ⊕ D.Carrier) := by
    have h := congrArg E.trace.presentation.continuous.connectedComponentsMap hx
    simpa [CutCapTopology.cappedChild, ← hq] using h
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  cases hf : E.trace.presentation (E.trace.capping.coreInclusion x.1) with
  | inl y =>
    have hy : ConnectedComponents.mk y = c := by
      have h := congrArg hret.connectedComponentsMap hpres
      simpa [retraction, hf, hq] using h
    refine ⟨⟨y, hy⟩, rfl, ?_⟩
    intro z hz
    apply Subtype.ext
    exact Sum.inl.inj hz.symm
  | inr d =>
    let tag : Q.Carrier ⊕ D.Carrier → Bool := Sum.elim (fun _ => false) (fun _ => true)
    have htag : Continuous tag := continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩
    have htagEq : (ConnectedComponents.mk true : ConnectedComponents Bool) =
        ConnectedComponents.mk false := by
      simpa [tag, hf] using congrArg htag.connectedComponentsMap hpres
    have hmem := ConnectedComponents.coe_eq_coe'.mp htagEq
    simp at hmem


def childCoreInclusionFun (c : ConnectedComponents Q.Carrier) : E.ChildCore c → E.ChildCarrier c :=
  fun x => Classical.choose (E.childCore_mapsTo_child c x)

theorem childCoreInclusionFun_eq (c : ConnectedComponents Q.Carrier) (x : E.ChildCore c) :
    E.trace.presentation (E.trace.capping.coreInclusion x.1) =
      Sum.inl (E.childCoreInclusionFun c x).1 :=
  (Classical.choose_spec (E.childCore_mapsTo_child c x)).1

theorem childCoreInclusion_continuous (c : ConnectedComponents Q.Carrier) :
    Continuous (E.childCoreInclusionFun c) := by
  obtain ⟨q, _⟩ := ConnectedComponents.surjective_coe c
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  apply continuous_induced_rng.2
  have h : Continuous (fun x : E.ChildCore c =>
      retraction (E.trace.presentation (E.trace.capping.coreInclusion x.1))) :=
    hret.comp (E.trace.presentation.continuous.comp
      (E.trace.capping.coreInclusion.continuous.comp continuous_subtype_val))
  apply h.congr
  intro x
  rw [E.childCoreInclusionFun_eq c x]
  rfl


def childCoreInclusion (c : ConnectedComponents Q.Carrier) : C(E.ChildCore c, E.ChildCarrier c) :=
  ⟨E.childCoreInclusionFun c, E.childCoreInclusion_continuous c⟩


theorem childCore_mem_parent (c : ConnectedComponents Q.Carrier) (x : E.ChildCore c) :
    ConnectedComponents.mk (x.1.1 : P.Carrier) = E.childParent c := by
  change continuous_subtype_val.connectedComponentsMap (ConnectedComponents.mk x.1) =
    continuous_subtype_val.connectedComponentsMap (E.childCoreComponent c)
  exact congrArg continuous_subtype_val.connectedComponentsMap x.2


def childCoreIntoParent (c : ConnectedComponents Q.Carrier) : C(E.ChildCore c, E.ParentCarrier c) :=
  ⟨fun x => ⟨x.1.1, E.childCore_mem_parent c x⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩


abbrev ChildCapBoundary (c : ConnectedComponents Q.Carrier) :=
  {b : E.trace.tubes.Boundary // ∀ y : Sphere 2,
    ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b y) = E.childCoreComponent c}

theorem childCap_mapsTo_child (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (x : ThreeBall) :
    ∃! q : E.ChildCarrier c,
      E.trace.presentation (E.trace.capping.cap b.1 x) = Sum.inl q.1 := by
  classical
  let : ConnectedSpace ThreeBall := isConnected_iff_connectedSpace.mp
    ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
  let y : Sphere 2 := ⟨EuclideanSpace.single 0 1, by
    simp [Sphere, PiLp.norm_single]⟩
  let z : E.ChildCore c :=
    ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y), b.2 _⟩
  let q := E.childCoreInclusionFun c z
  have hboundary : E.trace.presentation (E.trace.capping.cap b.1 (sphereToThreeBall y)) =
      Sum.inl q.1 := by
    rw [E.trace.capping.boundary_eq]
    exact E.childCoreInclusionFun_eq c z
  have hball : ConnectedComponents.mk x = ConnectedComponents.mk (sphereToThreeBall y) :=
    Subsingleton.elim _ _
  have hpres : ConnectedComponents.mk (E.trace.presentation (E.trace.capping.cap b.1 x)) =
      ConnectedComponents.mk (Sum.inl q.1 : Q.Carrier ⊕ D.Carrier) := by
    have h := congrArg
      (E.trace.presentation.continuous.comp (E.trace.capping.cap b.1).continuous).connectedComponentsMap
      hball
    exact h.trans (congrArg ConnectedComponents.mk hboundary)
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q.1)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  cases hf : E.trace.presentation (E.trace.capping.cap b.1 x) with
  | inl p =>
    have hp : ConnectedComponents.mk p = c := by
      have h := congrArg hret.connectedComponentsMap hpres
      simpa [retraction, hf, q.2] using h
    refine ⟨⟨p, hp⟩, rfl, ?_⟩
    intro w hw
    exact Subtype.ext (Sum.inl.inj hw.symm)
  | inr d =>
    let tag : Q.Carrier ⊕ D.Carrier → Bool := Sum.elim (fun _ => false) (fun _ => true)
    have htag : Continuous tag := continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩
    have htagEq : (ConnectedComponents.mk true : ConnectedComponents Bool) =
        ConnectedComponents.mk false := by
      simpa [tag, hf] using congrArg htag.connectedComponentsMap hpres
    have hmem := ConnectedComponents.coe_eq_coe'.mp htagEq
    simp at hmem


def childCapFun (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    ThreeBall → E.ChildCarrier c := fun x => Classical.choose (E.childCap_mapsTo_child c b x)

theorem childCapFun_eq (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (x : ThreeBall) : E.trace.presentation (E.trace.capping.cap b.1 x) =
      Sum.inl (E.childCapFun c b x).1 :=
  (Classical.choose_spec (E.childCap_mapsTo_child c b x)).1

theorem childCapFun_continuous (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Continuous (E.childCapFun c b) := by
  obtain ⟨q, _⟩ := ConnectedComponents.surjective_coe c
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  apply continuous_induced_rng.2
  have h : Continuous (fun x : ThreeBall => retraction
      (E.trace.presentation (E.trace.capping.cap b.1 x))) :=
    hret.comp (E.trace.presentation.continuous.comp (E.trace.capping.cap b.1).continuous)
  apply h.congr
  intro x
  rw [E.childCapFun_eq c b x]
  rfl


def childCap (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    C(ThreeBall, E.ChildCarrier c) := ⟨E.childCapFun c b, E.childCapFun_continuous c b⟩

theorem childCap_isEmbedding (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Topology.IsEmbedding (E.childCap c b) := by
  have hg : Topology.IsEmbedding (fun q : E.ChildCarrier c =>
      (Sum.inl q.1 : Q.Carrier ⊕ D.Carrier)) :=
    Topology.IsEmbedding.inl.comp Topology.IsEmbedding.subtypeVal
  apply hg.of_comp_iff.mp
  have hf : (fun x : ThreeBall => (Sum.inl (E.childCap c b x).1 : Q.Carrier ⊕ D.Carrier)) =
      E.trace.presentation ∘ E.trace.capping.cap b.1 := by
    funext x
    exact (E.childCapFun_eq c b x).symm
  change Topology.IsEmbedding (fun x : ThreeBall =>
    (Sum.inl (E.childCap c b x).1 : Q.Carrier ⊕ D.Carrier))
  rw [hf]
  exact E.trace.presentation.isEmbedding.comp (E.trace.capping.capEmbedding b.1)


theorem childCap_boundary_eq (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (y : Sphere 2) : E.childCap c b (sphereToThreeBall y) =
      E.childCoreInclusion c
        ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y), b.2 _⟩ := by
  apply Subtype.ext
  apply Sum.inl.inj (β := D.Carrier)
  change Sum.inl (E.childCapFun c b (sphereToThreeBall y)).1 = _
  rw [← E.childCapFun_eq c b (sphereToThreeBall y), E.trace.capping.boundary_eq]
  exact E.childCoreInclusionFun_eq c
    ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y), b.2 _⟩

def childCarrierOpenCover (E : SmoothCutCapTransition P Q D N) : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).toClosedOrientedManifold.Carrier →
    ∃ (U V : Set (E.ChildCarrier c)) (x₀ : E.ChildCarrier c),
      IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ x₀ ∈ U ∧ x₀ ∈ V ∧
      Set.range (E.childCoreInclusion c) ⊆ U ∧
      (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) ⊆ V ∧
      SimplyConnectedSpace U ∧ SimplyConnectedSpace V ∧
      PathConnectedSpace (↑(U ∩ V))

theorem child_simplyConnected_of_childCarrierOpenCover (E : SmoothCutCapTransition P Q D N)
    (h : E.childCarrierOpenCover) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).toClosedOrientedManifold.Carrier] :
    SimplyConnectedSpace (Q.component c).toClosedOrientedManifold.Carrier := by
  obtain ⟨U, V, x₀, hU, hV, hcov, hxU, hxV, _, _, hSU, hSV, hpc⟩ := h c inferInstance
  exact @DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_open_cover
    (E.ChildCarrier c) _ U V hU hV hcov x₀ ⟨hxU, hxV⟩ hSU hSV hpc

theorem childCore_compactSpace (c : ConnectedComponents Q.Carrier) : CompactSpace (E.ChildCore c) := by
  let := E.core_compact
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  have hs : ({y : E.trace.tubes.core | ConnectedComponents.mk y = E.childCoreComponent c} : Set _) =
      connectedComponent x := by
    ext y
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe'
  have hc : IsCompact ({y : E.trace.tubes.core |
      ConnectedComponents.mk y = E.childCoreComponent c} : Set _) := by
    rw [hs]
    exact isClosed_connectedComponent.isCompact
  exact isCompact_iff_compactSpace.mp hc

theorem childCoreInclusion_injective (c : ConnectedComponents Q.Carrier) :
    Function.Injective (E.childCoreInclusion c) := by
  intro x y h
  have hval : (E.childCoreInclusionFun c x).1 = (E.childCoreInclusionFun c y).1 :=
    congrArg Subtype.val h
  have hpres : E.trace.presentation (E.trace.capping.coreInclusion x.1) =
      E.trace.presentation (E.trace.capping.coreInclusion y.1) := by
    rw [E.childCoreInclusionFun_eq c x, E.childCoreInclusionFun_eq c y, hval]
  exact Subtype.ext (E.trace.capping.coreEmbedding.injective (E.trace.presentation.injective hpres))

theorem childCoreInclusion_isEmbedding (c : ConnectedComponents Q.Carrier) :
    Topology.IsEmbedding (E.childCoreInclusion c) := by
  let : CompactSpace (E.ChildCore c) := E.childCore_compactSpace c
  exact (Continuous.isClosedEmbedding (E.childCoreInclusion c).continuous
    (E.childCoreInclusion_injective c)).isEmbedding

theorem childCore_range_isSimplyConnected (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (E.ChildCore c)] :
    IsSimplyConnected (Set.range (E.childCoreInclusion c)) :=
  ((E.childCoreInclusion_isEmbedding c).toHomeomorph.toHomotopyEquiv).symm.simplyConnectedSpace

theorem childCap_range_isSimplyConnected (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    IsSimplyConnected (Set.range (E.childCap c b)) :=
  ((E.childCap_isEmbedding c b).toHomeomorph.toHomotopyEquiv).symm.simplyConnectedSpace

theorem range_childCoreInclusion_union_range_childCap
    (c : ConnectedComponents Q.Carrier) :
    Set.range (E.childCoreInclusion c) ∪
      (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = univ := by
  classical
  have hball : ConnectedSpace ThreeBall :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
  obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe c
  refine Set.eq_univ_of_forall fun v => ?_
  have hv : E.trace.presentation.symm (Sum.inl v.1) ∈
      Set.range E.trace.capping.coreInclusion ∪
        ⋃ b, Set.range (E.trace.capping.cap b) := by
    rw [E.trace.capping.exhaustive]
    trivial
  have hcap0 : E.trace.cappedChild (ConnectedComponents.mk q) =
      ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl q)) := by
    rw [CutCapTopology.cappedChild]
    rfl
  have hcapv : ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl v.1)) =
      ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl q)) := by
    have h := congrArg (E.trace.presentation.symm.continuous.comp continuous_inl).connectedComponentsMap
      (v.2 : ConnectedComponents.mk v.1 = ConnectedComponents.mk q)
    simpa using h
  have hcap : E.trace.cappedChild (ConnectedComponents.mk q) =
      ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl v.1)) :=
    hcap0.trans hcapv.symm
  have hcoreCompact : CompactSpace E.trace.tubes.core := E.core_compact
  have hcoreConnected : LocallyConnectedSpace E.trace.tubes.core := E.core_locallyConnected
  have hNt2 : T2Space N.Carrier := N.hausdorff
  have hcore : E.trace.capping.componentMap
      (E.childCoreComponent (ConnectedComponents.mk q)) =
      E.trace.cappedChild (ConnectedComponents.mk q) :=
    E.trace.capping.componentEquiv.apply_symm_apply _
  rcases hv with hv | hv
  · obtain ⟨x, hx⟩ := hv
    have hpres : E.trace.presentation (E.trace.capping.coreInclusion x) = Sum.inl v.1 := by
      rw [hx, Homeomorph.apply_symm_apply]
    have hcap2 : ConnectedComponents.mk (E.trace.capping.coreInclusion x) =
        E.trace.cappedChild (ConnectedComponents.mk q) := by
      rw [hcap, hx]
    have hchild : ConnectedComponents.mk x = E.childCoreComponent (ConnectedComponents.mk q) := by
      apply E.trace.capping.rfs_cap_component_bijection.injective
      rw [Capping.componentMap_mk, hcore]
      exact hcap2
    refine Or.inl ⟨⟨x, hchild⟩, ?_⟩
    apply Subtype.ext
    exact Sum.inl.inj ((E.childCoreInclusionFun_eq (ConnectedComponents.mk q)
      ⟨x, hchild⟩).symm.trans hpres)
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hv
    obtain ⟨z, hz⟩ := hb
    have hpres : E.trace.presentation (E.trace.capping.cap b z) = Sum.inl v.1 := by
      rw [hz, Homeomorph.apply_symm_apply]
    have hcap2 : ConnectedComponents.mk (E.trace.capping.cap b z) =
        E.trace.cappedChild (ConnectedComponents.mk q) := by
      rw [hcap, ← hz]
    have hpre : IsPreconnected (Set.range (E.trace.capping.cap b)) :=
      isPreconnected_range (E.trace.capping.cap b).continuous
    have hsame : ∀ y : Sphere 2,
        ConnectedComponents.mk (E.trace.capping.cap b (sphereToThreeBall y)) =
          ConnectedComponents.mk (E.trace.capping.cap b z) := fun y =>
      ConnectedComponents.coe_eq_coe'.mpr
        (hpre.subset_connectedComponent (Set.mem_range_self z)
          (Set.mem_range_self (sphereToThreeBall y)))
    have hbound : ∀ y : Sphere 2,
        ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b y) =
          E.childCoreComponent (ConnectedComponents.mk q) := by
      intro y
      have hpreB : IsPreconnected (Set.range (E.trace.tubes.coreBoundarySphere b)) := by
        have hsphere : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
          (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
            (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
        exact isPreconnected_range (E.trace.tubes.coreBoundarySphere b).continuous
      have hall : ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b y) =
          ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b
            (E.trace.capping.attaching b y)) :=
        ConnectedComponents.coe_eq_coe'.mpr
          (hpreB.subset_connectedComponent
            (Set.mem_range_self (E.trace.capping.attaching b y)) (Set.mem_range_self y))
      have hkey : ConnectedComponents.mk (E.trace.capping.coreInclusion
          (E.trace.tubes.coreBoundarySphere b (E.trace.capping.attaching b y))) =
          E.trace.cappedChild (ConnectedComponents.mk q) := by
        rw [← E.trace.capping.boundary_eq b y]
        exact (hsame y).trans hcap2
      rw [hall]
      apply E.trace.capping.rfs_cap_component_bijection.injective
      rw [Capping.componentMap_mk, hcore]
      exact hkey
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨b, hbound⟩, ?_⟩)
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact Sum.inl.inj ((E.childCapFun_eq (ConnectedComponents.mk q) ⟨b, hbound⟩ z).symm.trans hpres)

theorem retainedBoundary_of_mem_childCapBoundary
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    ∀ y : Sphere 2, E.trace.tubes.coreBoundarySphere b.1 y ∈ E.trace.retainedCore := by
  have hcoreCompact : CompactSpace E.trace.tubes.core := E.core_compact
  have hcoreConnected : LocallyConnectedSpace E.trace.tubes.core := E.core_locallyConnected
  have hNt2 : T2Space N.Carrier := N.hausdorff
  intro y
  exact CutCapTopology.childCore_subset_retainedCore E.trace c (b.2 y)
end SmoothCutCapTransition

namespace SmoothCutCapTransition

theorem childParent_congr {P Q D N P' Q' D' N' : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (F : SmoothCutCapTransition P' Q' D' N')
    (hp : P = P') (hq : Q = Q') (hd : D = D') (hn : N = N') (hEF : HEq E F)
    (c : ConnectedComponents Q.Carrier) :
    (hp ▸ E.childParent c) = F.childParent (hq ▸ c) := by
  cases hp
  cases hq
  cases hd
  cases hn
  cases eq_of_heq hEF
  rfl

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
