import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapSmoothGluing

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem discardedCoreInclusion_eq_discardedCap_boundary_of_isBoundaryPoint
    (x : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore})
    (hx : let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
        E.coreOpensCharts E.trace.discardedCoreOpen
      (𝓡∂ 3).IsBoundaryPoint x) :
    ∃ (b : E.trace.tubes.Boundary) (hb : E.trace.capDiscarded b) (y : Sphere 2),
      E.trace.discardedCoreInclusion x = E.trace.discardedCap b hb (sphereToThreeBall y) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.trace.tubes.core := E.coreCharts
  let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    E.coreOpensCharts E.trace.discardedCoreOpen
  let xOpen : E.trace.discardedCoreOpen := x
  have hxOpen : (𝓡∂ 3).IsBoundaryPoint xOpen := hx
  have hxCore : (𝓡∂ 3).IsBoundaryPoint x.1 :=
    (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val
      (I := 𝓡∂ 3) (u := E.trace.discardedCoreOpen) (x := xOpen)).mp hxOpen
  have hmem : x.1 ∈ (𝓡∂ 3).boundary E.trace.tubes.core := hxCore
  rw [E.core_boundary] at hmem
  obtain ⟨b, y, hy⟩ := mem_iUnion.mp hmem
  have hb : E.trace.capDiscarded b :=
    (E.trace.capDiscarded_iff_not_capRetained b).mpr fun h =>
      x.2 (hy ▸ E.trace.capRetained_coreBoundarySphere_mem_retainedCore b h y)
  refine ⟨b, hb, (E.trace.capping.attaching b).symm y, ?_⟩
  rw [E.trace.discardedCap_boundary]
  apply congrArg E.trace.discardedCoreInclusion
  apply Subtype.ext
  change x.1 = E.trace.tubes.coreBoundarySphere b
    (E.trace.capping.attaching b ((E.trace.capping.attaching b).symm y))
  rw [(E.trace.capping.attaching b).apply_symm_apply, hy]

end SmoothCutCapTransition

namespace GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  {V HY Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HY] [TopologicalSpace Y] [ChartedSpace HY Y]
  (J : ModelWithCorners ℝ V HY)
  [hCompact : CompactSpace {x : (H.event i).transition.trace.tubes.core //
    x ∉ (H.event i).transition.trace.retainedCore}]
  (fCore : C({x : (H.event i).transition.trace.tubes.core //
    x ∉ (H.event i).transition.trace.retainedCore}, Y))
  (fCap : (b : {b : (H.event i).transition.trace.tubes.Boundary //
    (H.event i).transition.trace.capDiscarded b}) → C(ThreeBall, Y))
  (hboundary : ∀ (b : {b : (H.event i).transition.trace.tubes.Boundary //
      (H.event i).transition.trace.capDiscarded b}) (y : Sphere 2),
    fCap b (sphereToThreeBall y) = fCore
      ⟨(H.event i).transition.trace.tubes.coreBoundarySphere b.1
          ((H.event i).transition.trace.capping.attaching b.1 y),
        (H.event i).transition.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore
          b.1 b.2 _⟩)

include hCompact

theorem discardedDesc_contMDiff_of_collar_profiles
    (hfCore : let : ChartedSpace (EuclideanHalfSpace 3) {x : (H.event i).transition.trace.tubes.core //
          x ∉ (H.event i).transition.trace.retainedCore} :=
        (H.event i).transition.coreOpensCharts (H.event i).transition.trace.discardedCoreOpen
      ∀ x, (𝓡∂ 3).IsInteriorPoint x → ContMDiffAt (𝓡∂ 3) J ∞ fCore x)
    (hfCap : let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := (H.event i).transition.ballCharts
      ∀ b x, (𝓡∂ 3).IsInteriorPoint x → ContMDiffAt (𝓡∂ 3) J ∞ (fCap b) x)
    (c : (b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b}) →
      DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun y : Sphere 2 =>
          (H.event i).transition.trace.discardedCap b.1 b.2 (sphereToThreeBall y)))
    (hwidth : ∀ b, (c b).radius ≤ cuttingCollarWidth (G.delta b.1.1))
    (capSide : (b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b}) →
      {q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval (c b).radius //
        q.2.1 ≤ 0} → ThreeBall)
    (hcore : ∀ b q (hq : 0 ≤ q.2.1), (c b).toFun q = G.discardedCoreCollar b.1 b.2
      ((H.event i).transition.trace.capping.attaching b.1 q.1,
        ⟨q.2.1, hq, lt_of_lt_of_le q.2.2.2 (hwidth b)⟩))
    (hcap : ∀ b q (hq : q.2.1 ≤ 0), (c b).toFun q =
      (H.event i).transition.trace.discardedCap b.1 b.2 (capSide b ⟨q, hq⟩))
    (profile : (b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b}) →
      Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval (c b).radius → Y)
    (hsmooth : ∀ b, ContMDiff ((𝓡 2).prod 𝓘(ℝ)) J ∞ (profile b))
    (hprofileCore : ∀ b q (hq : 0 ≤ q.2.1), profile b q = fCore
      ⟨G.coreCollar b.1 ((H.event i).transition.trace.capping.attaching b.1 q.1,
          ⟨q.2.1, hq, lt_of_lt_of_le q.2.2.2 (hwidth b)⟩),
        G.coreCollar_not_mem_retainedCore_of_capDiscarded b.1 b.2 sphereNorth _⟩)
    (hprofileCap : ∀ b q (hq : q.2.1 ≤ 0), profile b q = fCap b (capSide b ⟨q, hq⟩)) :
    ContMDiff ThreeModel J ∞ ((H.event i).transition.trace.discardedDesc fCore fCap hboundary) := by
  let : ChartedSpace (EuclideanHalfSpace 3) {x : (H.event i).transition.trace.tubes.core //
        x ∉ (H.event i).transition.trace.retainedCore} :=
    (H.event i).transition.coreOpensCharts (H.event i).transition.trace.discardedCoreOpen
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := (H.event i).transition.ballCharts
  have hseam : ∀ (b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b}) (y : Sphere 2),
      ContMDiffAt ThreeModel J ∞ ((H.event i).transition.trace.discardedDesc fCore fCap hboundary)
        ((H.event i).transition.trace.discardedCap b.1 b.2 (sphereToThreeBall y)) := by
    intro b y
    have hs := G.discardedDesc_contMDiffOn_of_collar_profile J fCore fCap hboundary
      b.1 b.2 (c b) (hwidth b) (capSide b) (hcore b) (hcap b)
      (profile b) (hsmooth b) (hprofileCore b) (hprofileCap b)
    have hy : (H.event i).transition.trace.discardedCap b.1 b.2 (sphereToThreeBall y) ∈
        (c b).neighborhood := by
      rw [← (c b).zero_eq y]
      exact ((c b).toDiffeomorph
        (y, ⟨0, neg_lt_zero.mpr (c b).radius_pos, (c b).radius_pos⟩)).2
    exact hs.contMDiffAt ((c b).neighborhood.isOpen.mem_nhds hy)
  intro d
  have hd : d ∈ range (H.event i).transition.trace.discardedCoreInclusion ∪
      (⋃ b : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b},
        range ((H.event i).transition.trace.discardedCap b.1 b.2)) := by
    rw [(H.event i).transition.trace.discardedCoreInclusion_union_discardedCaps]
    exact mem_univ d
  rcases hd with ⟨x, rfl⟩ | hd
  · rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · exact (H.event i).transition.discardedDesc_contMDiffAt_core_of_isInteriorPoint
        J fCore fCap hboundary le_rfl x hx (hfCore x hx)
    · obtain ⟨b, hb, y, hy⟩ :=
        (H.event i).transition.discardedCoreInclusion_eq_discardedCap_boundary_of_isBoundaryPoint
          x hx
      rw [hy]
      exact hseam ⟨b, hb⟩ y
  · obtain ⟨b, x, rfl⟩ := mem_iUnion.mp hd
    rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · exact (H.event i).transition.discardedDesc_contMDiffAt_cap_of_isInteriorPoint
        J fCore fCap hboundary le_rfl b x hx (hfCap b x hx)
    · have hxBoundary : x ∈ (𝓡∂ 3).boundary ThreeBall := hx
      rw [(H.event i).transition.ball_boundary] at hxBoundary
      obtain ⟨y, rfl⟩ := hxBoundary
      exact hseam b y

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
