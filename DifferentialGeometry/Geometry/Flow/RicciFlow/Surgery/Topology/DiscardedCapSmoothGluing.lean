import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapGluing
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  {V HY Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HY] [TopologicalSpace Y] [ChartedSpace HY Y]
  (J : ModelWithCorners ℝ V HY)


variable [hCompact : CompactSpace {x : (H.event i).transition.trace.tubes.core // x ∉ (H.event i).transition.trace.retainedCore}]
  (fCore : C({x : (H.event i).transition.trace.tubes.core // x ∉ (H.event i).transition.trace.retainedCore}, Y))
  (fCap : (b : {b : (H.event i).transition.trace.tubes.Boundary // (H.event i).transition.trace.capDiscarded b}) → C(ThreeBall, Y))
  (hboundary : ∀ (b : {b : (H.event i).transition.trace.tubes.Boundary // (H.event i).transition.trace.capDiscarded b}) (y : Sphere 2),
    fCap b (sphereToThreeBall y) = fCore
      ⟨(H.event i).transition.trace.tubes.coreBoundarySphere b.1 ((H.event i).transition.trace.capping.attaching b.1 y),
        (H.event i).transition.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore b.1 b.2 _⟩)

include hCompact

theorem discardedDesc_contMDiffOn_of_collar_profile
    (b : (H.event i).transition.trace.tubes.Boundary) (hb : (H.event i).transition.trace.capDiscarded b)
    (c : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
      (fun y : Sphere 2 => (H.event i).transition.trace.discardedCap b hb (sphereToThreeBall y)))
    (hwidth : c.radius ≤ cuttingCollarWidth (G.delta b.1))
    (capSide : {q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius //
        q.2.1 ≤ 0} → ThreeBall)
    (hcore : ∀ q (hq : 0 ≤ q.2.1), c.toFun q = G.discardedCoreCollar b hb
      ((H.event i).transition.trace.capping.attaching b q.1, ⟨q.2.1, hq, lt_of_lt_of_le q.2.2.2 hwidth⟩))
    (hcap : ∀ q (hq : q.2.1 ≤ 0), c.toFun q = (H.event i).transition.trace.discardedCap b hb (capSide ⟨q, hq⟩))
    (profile : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius → Y)
    (hsmooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) J ∞ profile)
    (hprofileCore : ∀ q (hq : 0 ≤ q.2.1), profile q = fCore
      ⟨G.coreCollar b ((H.event i).transition.trace.capping.attaching b q.1,
          ⟨q.2.1, hq, lt_of_lt_of_le q.2.2.2 hwidth⟩),
        G.coreCollar_not_mem_retainedCore_of_capDiscarded b hb sphereNorth _⟩)
    (hprofileCap : ∀ q (hq : q.2.1 ≤ 0), profile q = fCap ⟨b, hb⟩ (capSide ⟨q, hq⟩)) :
    ContMDiffOn ThreeModel J ∞ ((H.event i).transition.trace.discardedDesc fCore fCap hboundary) c.neighborhood := by
  have hcomp : ((H.event i).transition.trace.discardedDesc fCore fCap hboundary : (H.event i).discarded.Carrier → Y) ∘ c.toFun = profile := by
    funext q
    rcases le_total 0 q.2.1 with hq | hq
    · change (H.event i).transition.trace.discardedDesc fCore fCap hboundary (c.toFun q) = profile q
      rw [hcore q hq]
      change (H.event i).transition.trace.discardedDesc fCore fCap hboundary ((H.event i).transition.trace.discardedCoreInclusion _) = profile q
      rw [(H.event i).transition.trace.discardedDesc_core]
      exact (hprofileCore q hq).symm
    · change (H.event i).transition.trace.discardedDesc fCore fCap hboundary (c.toFun q) = profile q
      rw [hcap q hq, (H.event i).transition.trace.discardedDesc_cap fCore fCap hboundary ⟨b, hb⟩]
      exact (hprofileCap q hq).symm
  have hrestriction : (fun z : c.neighborhood => (H.event i).transition.trace.discardedDesc fCore fCap hboundary z.1) =
      profile ∘ c.toDiffeomorph.symm := by
    funext z
    have h := congrFun hcomp (c.toDiffeomorph.symm z)
    simpa only [Function.comp_apply, DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun,
      c.toDiffeomorph.apply_symm_apply] using h
  have hlocal : ContMDiff ThreeModel J ∞
      (fun z : c.neighborhood => (H.event i).transition.trace.discardedDesc fCore fCap hboundary z.1) := by
    rw [hrestriction]
    exact hsmooth.comp c.toDiffeomorph.symm.contMDiff
  intro d hd
  exact (contMDiffAt_subtype_iff.mp (hlocal ⟨d, hd⟩)).contMDiffWithinAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
