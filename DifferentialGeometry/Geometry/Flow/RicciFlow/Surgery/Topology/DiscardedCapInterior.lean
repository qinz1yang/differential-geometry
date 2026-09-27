import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OpenCoreSubmanifold
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInterior
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingRestriction

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N] (E : CutCapTopology M Q D N)

abbrev discardedCoreOpen : TopologicalSpace.Opens E.tubes.core :=
  ⟨E.retainedCoreᶜ, E.isClopen_retainedCore.compl.isOpen⟩

@[simp] theorem discardedCoreOpen_coe :
    (E.discardedCoreOpen : Set E.tubes.core) = E.retainedCoreᶜ := rfl

end CutCapTopology

namespace SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem discardedCoreInclusion_isSmoothEmbedding :
    let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
      E.coreOpensCharts E.trace.discardedCoreOpen
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ E.trace.discardedCoreInclusion := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.trace.tubes.core := E.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.trace.tubes.core := E.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    E.coreOpensCharts E.trace.discardedCoreOpen
  have hcore : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : E.trace.discardedCoreOpen => E.trace.capping.coreInclusion x.val) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
      (𝓡∂ 3) ThreeModel E.trace.capping.coreInclusion E.core_inclusion_smooth
      E.trace.discardedCoreOpen
  have hinr : IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (Sum.inr : D.Carrier → Q.Carrier ⊕ D.Carrier) := by
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      ContMDiff.inr
    · intro x
      rw [mfderiv_sumInr]
      exact Function.injective_id
    · rfl
  apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph hinr
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
      (𝓡∂ 3) ThreeModel _ hcore E.presentation)
    E.trace.discardedCoreInclusion.continuous
  intro x
  simp only [Function.comp_apply]
  rw [E.trace.inr_discardedCoreInclusion, E.presentation_eq]

variable {V HY Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HY] [TopologicalSpace Y] [ChartedSpace HY Y]
  (J : ModelWithCorners ℝ V HY)
  [hCompact : CompactSpace {x : E.trace.tubes.core // x ∉ E.trace.retainedCore}]
  (fCore : C({x : E.trace.tubes.core // x ∉ E.trace.retainedCore}, Y))
  (fCap : (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) → C(ThreeBall, Y))
  (hboundary : ∀ (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) (y : Sphere 2),
    fCap b (sphereToThreeBall y) = fCore
      ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y),
        E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore b.1 b.2 _⟩)

include hCompact

theorem discardedDesc_contMDiffAt_core_of_isInteriorPoint
    {n : ℕ∞ω} (hn : n ≤ ∞) (x : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore})
    (hx : let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
        E.coreOpensCharts E.trace.discardedCoreOpen
      (𝓡∂ 3).IsInteriorPoint x)
    (hfCore : let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
        E.coreOpensCharts E.trace.discardedCoreOpen
      ContMDiffAt (𝓡∂ 3) J n fCore x) :
    ContMDiffAt ThreeModel J n (E.trace.discardedDesc fCore fCap hboundary)
      (E.trace.discardedCoreInclusion x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.trace.tubes.core := E.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.trace.tubes.core := E.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    E.coreOpensCharts E.trace.discardedCoreOpen
  let : IsManifold (𝓡∂ 3) ∞ {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    inferInstanceAs (IsManifold (𝓡∂ 3) ∞ E.trace.discardedCoreOpen)
  have he : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ E.trace.discardedCoreInclusion :=
    E.discardedCoreInclusion_isSmoothEmbedding
  apply he.contMDiffAt_of_comp_of_isInteriorPoint hn (by simp [ThreeSpace]) hx
  have hcomp : (E.trace.discardedDesc fCore fCap hboundary : D.Carrier → Y) ∘
      E.trace.discardedCoreInclusion = fCore :=
    funext (E.trace.discardedDesc_core fCore fCap hboundary)
  rw [hcomp]
  exact hfCore

theorem discardedDesc_contMDiffAt_cap_of_isInteriorPoint
    {n : ℕ∞ω} (hn : n ≤ ∞) (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b})
    (x : ThreeBall)
    (hx : let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
      (𝓡∂ 3).IsInteriorPoint x)
    (hfCap : let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
      ContMDiffAt (𝓡∂ 3) J n (fCap b) x) :
    ContMDiffAt ThreeModel J n (E.trace.discardedDesc fCore fCap hboundary)
      (E.trace.discardedCap b.1 b.2 x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  have he : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (E.trace.discardedCap b.1 b.2) :=
    E.discardedCap_isSmoothEmbedding b.1 b.2
  apply he.contMDiffAt_of_comp_of_isInteriorPoint hn (by simp [ThreeSpace]) hx
  have hcomp : (E.trace.discardedDesc fCore fCap hboundary : D.Carrier → Y) ∘
      E.trace.discardedCap b.1 b.2 = fCap b :=
    funext (E.trace.discardedDesc_cap fCore fCap hboundary b)
  rw [hcomp]
  exact hfCap

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
