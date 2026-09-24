import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCoreComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapCoreCapping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapSide
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapComponent

noncomputable section

section


open Set
open scoped Manifold
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem image_capCore_union_cap_eq_componentSet
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ T.core)
    (b : T.Boundary) (hfront : frontier K = range (T.boundarySphere b))
    (x : T.core) (hx : x.val ∈ K) :
    C.coreInclusion '' (Subtype.val ⁻¹' K : Set T.core) ∪ range (C.cap b) =
      N.componentSet (ConnectedComponents.mk (C.coreInclusion x)) := by
  have hcomp : connectedComponent x = (Subtype.val ⁻¹' K : Set T.core) :=
    T.toTopological.connectedComponent_eq_preimage_of_capCore_of_boundarySphere
      cap hK b hfront (T.smooth b.1) x hx
  rw [ClosedOrientedManifold.componentSet_mk, ← hcomp]
  apply C.image_coreComponent_union_cap_eq_connectedComponent x b
  · intro z
    rw [hcomp]
    change T.boundarySphere b z ∈ K
    exact cap.isCompact_carrier.isClosed.frontier_subset (hfront.symm ▸ mem_range_self z)
  · intro b' hb'
    obtain ⟨z, hz⟩ := hb'
    rw [hcomp] at hz
    exact T.toTopological.eq_of_boundarySphere_mem_of_frontier_eq hK b hfront hz

end DifferentialGeometry.Topology.SphericalCapping

end

section


open Set
open DifferentialGeometry.PDE.RicciFlow (SolutionOn)
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_capCore_frontier
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ T.core)
    (b : T.Boundary) (hfront : frontier K = range (T.boundarySphere b))
    (x : T.core) (hx : x.val ∈ K) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier :=
  C.isPoincareStandard_component_of_capCore_and_cap_cover cap hK b _
    (C.image_capCore_union_cap_eq_componentSet cap hK b hfront x hx)

theorem exists_isPoincareStandard_component_of_spatialNeck_center_close
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M.Carrier) J}
    {eps epsc t : ℝ} {x p : M.Carrier} {U : Set M.Carrier} (cap : LocalCap S epsc x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p) (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 →
      T.tube a q = nk.map (q.1, q.2.val))
    (hclose : riemannianEDistOf (S.base.metric t) x p +
      ENNReal.ofReal (7 * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) <
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)))
    (hanchor : ∀ j : T.Index, j ≠ a → ∃ z ∈ T.removedBand j, z ∉ interior cap.core.carrier) :
    ∃ (side : Bool) (K : Set M.Carrier), Nonempty (CapCore K) ∧
      K ⊆ interior cap.core.carrier ∧ frontier K = range (T.boundarySphere (a, side)) ∧
      K ⊆ T.core ∧ ∀ z : T.core, z.val ∈ K →
        isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion z))).Carrier := by
  obtain ⟨side, K, hK, hKU, hfront, hcore⟩ :=
    T.toTopological.exists_capCore_in_cutCore_of_spatialNeck_center_close
      cap hdepth nk a hmap hclose hanchor
  exact ⟨side, K, hK, hKU, hfront, hcore, fun z hz =>
    C.isPoincareStandard_component_of_capCore_frontier
      hK.some hcore (a, side) hfront z hz⟩

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_capCore_frontier
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ E.tubes.core)
    (b : E.tubes.Boundary) (hfront : frontier K = range (E.tubes.boundarySphere b))
    (x : E.tubes.core) (hx : x.val ∈ K) (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier :=
  E.isPoincareStandard_discardedComponent_of_capCore_and_cap_cover cap hK b x d hd
    (E.capping.image_capCore_union_cap_eq_componentSet cap hK b hfront x hx)

end DifferentialGeometry.Topology.SphericalCutCapTransition

end

section


open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow (SolutionOn)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u
variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem exists_isPoincareStandard_discardedComponent_of_spatialNeck_center_close
    (hc : SmoothCutCapCompletion E)
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.Carrier) J}
    {eps epsc C1 C2 t : ℝ} {x p : P.Carrier}
    (W : CanonicalWitness S epsc C1 C2 x t)
    (cap : LocalCap S epsc x t W.domain.carrier)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p) (a : E.trace.tubes.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 →
      E.trace.tubes.tube a q = nk.map (q.1, q.2.val))
    (hclose : riemannianEDistOf (S.base.metric t) x p +
      ENNReal.ofReal (7 * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) <
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)))
    (hanchor : ∀ j : E.trace.tubes.Index, j ≠ a →
      ∃ z ∈ E.trace.tubes.removedBand j, z ∉ interior cap.core.carrier)
    (hlow : ∀ z : E.trace.tubes.core, z ∈ E.trace.retainedCore →
      ∃ y : E.trace.tubes.core, ConnectedComponents.mk y = ConnectedComponents.mk z ∧
        C2 * S.scalar t y.val < S.scalar t x) :
    ∃ (side : Bool) (K : Set P.Carrier), Nonempty (CapCore K) ∧
      K ⊆ interior cap.core.carrier ∧ frontier K = range (E.trace.tubes.boundarySphere (a, side)) ∧
      K ⊆ E.trace.tubes.core ∧ ∀ z : E.trace.tubes.core, z.val ∈ K →
        ∃ d : D.Carrier, E.trace.presentation (E.trace.capping.coreInclusion z) = Sum.inr d ∧
          DifferentialGeometry.Topology.isPoincareStandard
            (D.toClosedOrientedManifold.component (ConnectedComponents.mk d)).Carrier := by
  let R : Set (ConnectedComponents E.trace.tubes.core) :=
    ConnectedComponents.mk '' E.trace.retainedCore
  have hR : ∀ c ∈ R, ∃ y : E.trace.tubes.core, ConnectedComponents.mk y = c ∧
      C2 * S.scalar t y.val < S.scalar t x := by
    rintro c ⟨z, hz, rfl⟩
    exact hlow z hz
  obtain ⟨side, K, hK, hKU, hfront, hcore, _, hdiscard⟩ :=
    E.trace.tubes.exists_capCore_discarded_component_of_spatialNeck_center_close
      W cap hdepth nk a hmap hclose hanchor R hR
  refine ⟨side, K, hK, hKU, hfront, hcore, ?_⟩
  intro z hz
  have hn : z ∉ E.trace.retainedCore := fun h => hdiscard z hz ⟨z, h, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : D.Carrier,
      E.trace.presentation (E.trace.capping.coreInclusion z) = Sum.inr d := by
    cases hp : E.trace.presentation (E.trace.capping.coreInclusion z) with
    | inl q => exact (hn ⟨q, hp⟩).elim
    | inr d => exact ⟨d, rfl⟩
  refine ⟨d, hd, ?_⟩
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition E hc
  have hdx : X.presentation (X.capping.coreInclusion z) = Sum.inr d :=
    (congrArg E.presentation
      (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion E hc z)).trans
        ((congrFun E.presentation_eq _).trans hd)
  exact X.isPoincareStandard_discardedComponent_of_capCore_frontier
    hK.some hcore (a, side) hfront z hz d hdx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

end

end

section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
theorem exists_isPoincareStandard_discardedComponent_of_terminal_cap_boundary_capture
    (hc : SmoothCutCapCompletion (H.event i).transition)
    {U : Set (H.event i).incoming.terminalRegularOpen} (cap : CapCore U)
    (hscalar : ∀ y ∈ interior U,
      ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
        metricScalarAt (H.event i).terminal.metric y)
    (j : (H.event i).transition.trace.tubes.Index)
    (hinside : ∀ side : Bool, range ((H.event i).transition.trace.tubes.boundarySphere (j, side)) ⊆
      (Subtype.val : (H.event i).incoming.terminalRegularOpen → (H.stage i.castSucc).Carrier) ''
        interior U) :
    ∃ (b : (H.event i).transition.trace.tubes.Boundary) (K : Set (H.stage i.castSucc).Carrier), Nonempty (CapCore K) ∧
      K ⊆ (Subtype.val : (H.event i).incoming.terminalRegularOpen → (H.stage i.castSucc).Carrier) ''
        interior U ∧
      frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
      K ⊆ (H.event i).transition.trace.tubes.core ∧
      ∀ z : (H.event i).transition.trace.tubes.core, z.val ∈ K →
        ∃ d : (H.event i).discarded.Carrier,
          (H.event i).transition.trace.presentation
            ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d ∧
          DifferentialGeometry.Topology.isPoincareStandard
            ((H.event i).discarded.toClosedOrientedManifold.component
              (ConnectedComponents.mk d)).Carrier := by
  obtain ⟨b, K, hK, hKU, hfront, hcore, _, hdiscard⟩ :=
    G.exists_discarded_capCore_component_of_terminal_cap_boundary_capture cap hscalar j hinside
  refine ⟨b, K, hK, hKU, hfront, hcore, ?_⟩
  intro z hz
  obtain ⟨d, hd⟩ : ∃ d : (H.event i).discarded.Carrier,
      (H.event i).transition.trace.presentation
        ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr d := by
    cases hp : (H.event i).transition.trace.presentation
        ((H.event i).transition.trace.capping.coreInclusion z) with
    | inl q => exact (hdiscard z hz ⟨q, hp⟩).elim
    | inr d => exact ⟨d, rfl⟩
  refine ⟨d, hd, ?_⟩
  let X := SphericalCutCapTransition.ofSmoothCutCapTransition (H.event i).transition hc
  have hdx : X.presentation (X.capping.coreInclusion z) = Sum.inr d :=
    (congrArg (H.event i).transition.presentation
      (SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
        (H.event i).transition hc z)).trans
        ((congrFun (H.event i).transition.presentation_eq _).trans hd)
  exact X.isPoincareStandard_discardedComponent_of_capCore_frontier
    hK.some hcore b hfront z hz d hdx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

end
