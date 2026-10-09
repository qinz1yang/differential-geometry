import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCoreComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapCoreCapping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapSide
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSpatialNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCoreGeometry

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
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_capCore_frontier
    cap hK b hfront x hx
  obtain ⟨e⟩ := E.cappedDiscardedPresentationRealization x d hd
  exact isPoincareStandard_of_diffeomorph e.val.symm hstd

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

theorem exists_isPoincareStandard_discardedComponent_of_capCore_frontier
    (hc : SmoothCutCapCompletion E)
    {K : Set P.Carrier} (cap : CapCore K) (hcore : K ⊆ E.trace.tubes.core)
    (b : E.trace.tubes.Boundary) (hfront : frontier K = range (E.trace.tubes.boundarySphere b))
    (z : E.trace.tubes.core) (hz : z.val ∈ K) (hn : z ∉ E.trace.retainedCore) :
    ∃ d : D.Carrier, E.trace.presentation (E.trace.capping.coreInclusion z) = Sum.inr d ∧
      DifferentialGeometry.Topology.isPoincareStandard
        (D.toClosedOrientedManifold.component (ConnectedComponents.mk d)).Carrier := by
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
    cap hcore b hfront z hz d hdx

theorem exists_isPoincareStandard_discardedComponent_of_capCore_frontier_of_scalar_gap
    (hc : SmoothCutCapCompletion E)
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.Carrier) J}
    {eps C1 C2 t : ℝ} {x : P.Carrier}
    (W : CanonicalWitness S eps C1 C2 x t)
    {K : Set P.Carrier} (cap : CapCore K) (hKU : K ⊆ W.domain.carrier)
    (hcore : K ⊆ E.trace.tubes.core) (b : E.trace.tubes.Boundary)
    (hfront : frontier K = range (E.trace.tubes.boundarySphere b))
    (z : E.trace.tubes.core) (hz : z.val ∈ K)
    (hlow : z ∈ E.trace.retainedCore →
      ∃ y : E.trace.tubes.core, ConnectedComponents.mk y = ConnectedComponents.mk z ∧
        C2 * S.scalar t y.val < S.scalar t x) :
    ∃ d : D.Carrier, E.trace.presentation (E.trace.capping.coreInclusion z) = Sum.inr d ∧
      DifferentialGeometry.Topology.isPoincareStandard
        (D.toClosedOrientedManifold.component (ConnectedComponents.mk d)).Carrier := by
  have hcomponent : connectedComponent z = (Subtype.val ⁻¹' K : Set E.trace.tubes.core) :=
    E.trace.tubes.connectedComponent_eq_preimage_of_capCore_of_boundarySphere
      cap hcore b hfront (E.tube_smooth b.1) z hz
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hn : z ∉ E.trace.retainedCore := by
    intro hret
    obtain ⟨y, hy, hscalar⟩ := hlow hret
    have hyK : y.val ∈ K := by
      change y ∈ (Subtype.val ⁻¹' K : Set E.trace.tubes.core)
      rw [← hcomponent]
      exact ConnectedComponents.coe_eq_coe'.mp hy
    have hbound := mul_le_mul_of_nonneg_left (W.scalar_bounds y.val (hKU hyK)).1 hC2.le
    rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hbound
    exact hscalar.not_ge hbound
  exact E.exists_isPoincareStandard_discardedComponent_of_capCore_frontier
    hc cap hcore b hfront z hz hn


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
  obtain ⟨side, K, hK, hKU, hfront, hcore⟩ :=
    E.trace.tubes.exists_capCore_in_cutCore_of_spatialNeck_center_close
      cap hdepth nk a hmap hclose hanchor
  refine ⟨side, K, hK, hKU, hfront, hcore, ?_⟩
  intro z hz
  exact E.exists_isPoincareStandard_discardedComponent_of_capCore_frontier_of_scalar_gap
    hc W hK.some (hKU.trans (interior_subset.trans (cap.core_inside.trans interior_subset)))
    hcore (a, side) hfront z hz (hlow z)

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
  exact (H.event i).transition.exists_isPoincareStandard_discardedComponent_of_capCore_frontier
    hc hK.some hcore b hfront z hz (hdiscard z hz)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

end

section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (R : GeometricCutoffRecord H i parameters)

include R in
theorem exists_late_isPoincareStandard_discardedComponent_of_cap
    (hc : SmoothCutCapCompletion (H.event i).transition)
    {eps η : ℝ} (hsmall : eps < 1 / 11) (heps : ∀ j, R.delta j ≤ eps) (hη : 0 < η) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ),
      ∀ t ∈ Ioo d (H.time i.succ), ∀ (epsc C1 C2 : ℝ) (x : (H.stage i.castSucc).Carrier),
        ∀ (W : CanonicalWitness (H.event i).incoming.flow epsc C1 C2 x t)
          (cap : LocalCap (H.event i).incoming.flow epsc x t W.domain.carrier),
          (∀ y ∈ cap.tube, 10000 / Real.sqrt ((H.event i).incoming.flow.scalar t x) ≤
            metricDistance ((H.event i).incoming.flow.base.metric t) x y) →
          ∀ j : (H.event i).transition.trace.tubes.Index,
            riemannianEDistOf ((H.event i).incoming.flow.base.metric t) x (R.neck j).center.val +
              ENNReal.ofReal (7 * Real.sqrt (1 + eps) /
                Real.sqrt (metricScalarAt ((H.event i).incoming.flow.base.metric t) (R.neck j).center.val)) <
              ENNReal.ofReal (10000 / Real.sqrt ((H.event i).incoming.flow.scalar t x)) →
            C2 * (((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ + η) <
              (H.event i).incoming.flow.scalar t x →
            ∃ (b : (H.event i).transition.trace.tubes.Boundary)
              (K : Set (H.stage i.castSucc).Carrier), Nonempty (CapCore K) ∧
              K ⊆ interior cap.core.carrier ∧
              frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
              K ⊆ (H.event i).transition.trace.tubes.core ∧
              ∀ z : (H.event i).transition.trace.tubes.core, z.val ∈ K →
                ∃ y : (H.event i).discarded.Carrier,
                  (H.event i).transition.trace.presentation
                    ((H.event i).transition.trace.capping.coreInclusion z) = Sum.inr y ∧
                  DifferentialGeometry.Topology.isPoincareStandard
                    ((H.event i).discarded.toClosedOrientedManifold.component
                      (ConnectedComponents.mk y)).Carrier := by
  obtain ⟨d₀, hd₀, hnecks⟩ := R.exists_late_spatialNecks hsmall heps
  obtain ⟨d₁, hd₁, hgap⟩ := R.exists_late_retained_component_scalar_gap hη
  refine ⟨max d₀ d₁, ⟨hd₀.1.trans (le_max_left _ _), max_lt hd₀.2 hd₁.2⟩, ?_⟩
  intro t ht epsc C1 C2 x W cap hdepth j hclose hhigh
  have ht₀ : t ∈ Ioo d₀ (H.time i.succ) := ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
  have ht₁ : t ∈ Ioo d₁ (H.time i.succ) := ⟨(le_max_right _ _).trans_lt ht.1, ht.2⟩
  obtain ⟨nk, _, hmap⟩ := hnecks t ht₀ j
  have hinside := (H.event i).transition.trace.tubes.closedBand_subset_cap_core_interior_of_spatialNeck_center_close
    cap hdepth nk j (fun q _ => (hmap q).symm) hclose
  have hsmooth : ∀ b : (H.event i).transition.trace.tubes.Boundary,
      IsSmoothEmbedding I2 I3 ∞ ((H.event i).transition.trace.tubes.boundarySphere b) :=
    fun b => (H.event i).transition.trace.tubes.isSmoothEmbedding_boundarySphere b
      ((H.event i).transition.tube_smooth b.1)
  obtain ⟨b, K, hK, hKU, hfront, hcore⟩ :=
    (H.event i).transition.trace.tubes.exists_capCore_in_cutCore_of_captured_boundary_spheres
      j cap.coreModel hsmooth
      ((H.event i).transition.trace.tubes.central_and_boundary_spheres_subset_of_closedBand_subset
        j hinside).2
  refine ⟨b, K, hK, hKU, hfront, hcore, ?_⟩
  intro z hz
  exact (H.event i).transition.exists_isPoincareStandard_discardedComponent_of_capCore_frontier_of_scalar_gap
    hc W hK.some (hKU.trans (interior_subset.trans (cap.core_inside.trans interior_subset)))
    hcore b hfront z hz (hgap t ht₁ C2 (zero_le_one.trans W.one_le_comparison_constant) x hhigh z)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

end
