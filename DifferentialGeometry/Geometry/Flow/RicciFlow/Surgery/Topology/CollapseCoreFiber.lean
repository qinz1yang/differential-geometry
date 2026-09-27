import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Descendants

attribute [local instance]
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreCharts
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreSmooth

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem coreInclusion_not_mem_cap_of_interior (x : E.trace.tubes.core)
    (hx : (𝓡∂ 3).IsInteriorPoint x) (b : E.trace.tubes.Boundary) :
    E.trace.capping.coreInclusion x ∉ Set.range (E.trace.capping.cap b) := by
  intro h
  have hinter : E.trace.capping.coreInclusion x ∈
      Set.range E.trace.capping.coreInclusion ∩ Set.range (E.trace.capping.cap b) :=
    ⟨Set.mem_range_self x, h⟩
  rw [E.trace.capping.core_cap_intersection b] at hinter
  obtain ⟨y, hy⟩ := hinter
  have heq : E.trace.tubes.coreBoundarySphere b y = x :=
    E.trace.capping.coreEmbedding.injective hy
  have hb : x ∈ (𝓡∂ 3).boundary E.trace.tubes.core := by
    rw [E.core_boundary]
    exact Set.mem_iUnion.mpr ⟨b, y, heq⟩
  exact ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hb

theorem range_childCoreIntoParent_mem_nhds (c : ConnectedComponents Q.Carrier)
    (x : E.ChildCore c) (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    Set.range (E.childCoreIntoParent c) ∈ 𝓝 (E.childCoreIntoParent c x) := by
  have hU : {z : E.trace.tubes.core | ConnectedComponents.mk z = E.childCoreComponent c} ∈
      𝓝 x.1 := (E.childCore_isOpen c).mem_nhds x.2
  have hW : (Subtype.val : E.trace.tubes.core → P.Carrier) ''
      {z : E.trace.tubes.core | ConnectedComponents.mk z = E.childCoreComponent c} ∈
      𝓝 (x.1.1 : P.Carrier) :=
    DifferentialGeometry.Topology.immersion_image_mem_nhds
      (E.core_induced.isImmersion.isImmersionAt x.1) (by simp [ThreeSpace]) hx hU
  have hpre := (continuous_subtype_val.continuousAt
    (x := E.childCoreIntoParent c x)).preimage_mem_nhds hW
  apply Filter.mem_of_superset hpre
  rintro y ⟨z, hz, hzy⟩
  exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

theorem exists_childCore_interior_point (c : ConnectedComponents Q.Carrier) :
    ∃ x : E.ChildCore c, (𝓡∂ 3).IsInteriorPoint x.1 := by
  let := E.childCoreCharts c
  obtain ⟨x, hx⟩ := E.childCore_interior_nonempty c
  refine ⟨x, ?_⟩
  apply ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint x.1).mpr
  intro hb
  have hxc : x ∈ (𝓡∂ 3).boundary (E.ChildCore c) := by
    rw [E.childCore_boundary c]
    exact hb
  exact ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx hxc

end SmoothCutCapTransition

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace ComparisonSupport

variable (K : G.ComparisonSupport c)

private theorem localCollapse_mem_cap (b : G.ChildBoundary c)
    (w : Sphere 2 × Icc (K.level b) 0) :
    (G.static b.1).witness.collapse (K.collarParameter b w) ∈
      Set.range (G.static b.1).witness.cap := by
  let p := K.collarParameter b w
  by_cases htip : p.1.1.2 ≤ (G.static b.1).witness.tipCoordinate
  · rw [(G.static b.1).witness.collapse_tip p htip]
    obtain ⟨t, -, ht⟩ := (G.static b.1).witness.tip_interior
    exact ⟨t, ht⟩
  · have hz : p.1.1.2 ≤ 0 := by
      rw [show p.1.1.2 = (w.2 : ℝ) from K.collarParameter_snd b w]
      exact w.2.2.2
    have hr := (G.static b.1).witness.radial_range ⟨(lt_of_not_ge htip).le, hz⟩
    have hball : (G.static b.1).witness.radial p.1.1.2 • p.1.1.1.1 ∈
        standardCapClosedCore := by
      rw [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right, norm_smul,
        spherePoint_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact hr.2
    rw [(G.static b.1).witness.collapse_radial p (lt_of_not_ge htip) hz hball]
    rw [← (G.static b.1).witness.capChart_range]
    exact Set.mem_range_self _

private theorem childCoreInclusion_ne_cap (x : G.transition.ChildCore c)
    (hx : (𝓡∂ 3).IsInteriorPoint x.1) (b : G.ChildBoundary c) (t : ThreeBall) :
    (G.transition.childCoreInclusion c x).1 ≠
      (G.static b.1).inclusion ((G.static b.1).witness.cap t) := by
  intro h
  have heq : G.transition.trace.capping.coreInclusion x.1 =
      G.transition.trace.capping.cap b.1.1 t := by
    apply G.transition.trace.presentation.injective
    exact (G.transition.childCoreInclusionFun_eq c x).trans
      ((congrArg Sum.inl h).trans ((G.static b.1).cap_eq t).symm)
  exact G.transition.coreInclusion_not_mem_cap_of_interior x.1 hx b.1.1 ⟨t, heq.symm⟩

theorem rfs_whole_parent_map_preimage_childCoreInclusion (x : G.transition.ChildCore c)
    (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    K.rfs_whole_parent_map ⁻¹' {G.transition.childCoreInclusion c x} =
      {G.transition.childCoreIntoParent c x} := by
  ext y
  change K.rfs_whole_parent_map y = G.transition.childCoreInclusion c x ↔
    y = G.transition.childCoreIntoParent c x
  constructor
  · intro hy
    by_cases hs : y ∈ K.support.region
    · rw [K.support_eq] at hs
      rcases hs with hcore | hcollar
      · obtain ⟨z, rfl⟩ := hcore
        rw [K.rfs_whole_parent_map_childCore] at hy
        exact congrArg (G.transition.childCoreIntoParent c)
          (G.transition.childCoreInclusion_injective c hy)
      · obtain ⟨b, w, hw⟩ := Set.mem_iUnion.mp hcollar
        rw [← hw, K.rfs_whole_parent_map_collar] at hy
        obtain ⟨t, ht⟩ := K.localCollapse_mem_cap b w
        have h := congrArg Subtype.val hy
        rw [K.localCollapse_eq b _, ← ht] at h
        exact False.elim (childCoreInclusion_ne_cap x hx b t h.symm)
    · obtain ⟨b, hb⟩ := K.exterior_exists y hs
      rw [K.rfs_whole_parent_map_eq_tip_of_mem_exterior b hb] at hy
      obtain ⟨t, -, ht⟩ := (G.static b.1).witness.tip_interior
      have h := congrArg Subtype.val hy
      rw [K.tip_eq b, ← ht] at h
      exact False.elim (childCoreInclusion_ne_cap x hx b t h.symm)
  · rintro rfl
    exact K.rfs_whole_parent_map_childCore x

theorem rfs_whole_parent_map_locally_injective_at_childCore (x : G.transition.ChildCore c)
    (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    ∃ U ∈ 𝓝 (G.transition.childCoreIntoParent c x),
      Set.InjOn K.rfs_whole_parent_map U := by
  refine ⟨Set.range (G.transition.childCoreIntoParent c),
    G.transition.range_childCoreIntoParent_mem_nhds c x hx, ?_⟩
  rintro y ⟨y', rfl⟩ z ⟨z', rfl⟩ h
  rw [K.rfs_whole_parent_map_childCore, K.rfs_whole_parent_map_childCore] at h
  exact congrArg (G.transition.childCoreIntoParent c)
    (G.transition.childCoreInclusion_injective c h)

theorem exists_rfs_whole_parent_map_singleton_fiber :
    ∃ x : G.transition.ChildCore c,
      (𝓡∂ 3).IsInteriorPoint x.1 ∧
      K.rfs_whole_parent_map ⁻¹' {G.transition.childCoreInclusion c x} =
        {G.transition.childCoreIntoParent c x} := by
  obtain ⟨x, hx⟩ := G.transition.exists_childCore_interior_point c
  exact ⟨x, hx, K.rfs_whole_parent_map_preimage_childCoreInclusion x hx⟩

end ComparisonSupport
end GeometricCutoffRecord
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
