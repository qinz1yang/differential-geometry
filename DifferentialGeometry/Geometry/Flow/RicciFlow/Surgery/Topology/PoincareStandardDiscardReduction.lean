import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Poincare
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HextDiscardedSideReduction
import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSum

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def simplyConnectedPoincareStandard : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M], isPoincareStandard M

theorem simplyConnectedPoincareStandard_of_smoothPoincareConjecture
    (h : DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture.{u}) :
    simplyConnectedPoincareStandard.{u} := by
  intro M _ _ _ _ _ _ _
  obtain ⟨e⟩ := h M
  exact isPoincareStandard_of_diffeomorph e isPoincareStandard_sphere

theorem smoothPoincareConjecture_of_simplyConnectedPoincareStandard
    (h : simplyConnectedPoincareStandard.{u}) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _
  exact exists_diffeomorph_standardThreeSphere_of_isPoincareStandard (h M)

theorem smoothPoincareConjecture_iff_simplyConnectedPoincareStandard :
    DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture.{u} ↔
      simplyConnectedPoincareStandard.{u} :=
  ⟨simplyConnectedPoincareStandard_of_smoothPoincareConjecture,
    smoothPoincareConjecture_of_simplyConnectedPoincareStandard⟩

theorem subsingleton_fundamentalGroup_factor_of_subsingleton_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (F : ConnectedClosedOrientedManifold.{u} 3) (hF : F ∈ L)
    (x : (i : Fin L.length) → (L.get i).Carrier)
    (y : (finiteConnectedSum L).Carrier)
    (h : Subsingleton (FundamentalGroup (finiteConnectedSum L).Carrier y))
    (q : F.Carrier) : Subsingleton (FundamentalGroup F.Carrier q) := by
  obtain ⟨i, rfl⟩ := List.get_of_mem hF
  obtain ⟨e⟩ := fundamentalGroup_finiteConnectedSum_freeProduct L x y
  have hcoprod : Subsingleton (Monoid.CoprodI fun i : Fin L.length =>
      FundamentalGroup (L.get i).Carrier (x i)) :=
    @Equiv.subsingleton _ _ e.symm h
  have hx : Subsingleton (FundamentalGroup (L.get i).Carrier (x i)) :=
    (DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff _).mp hcoprod i
  exact subsingleton_fundamentalGroup_of_joined
    (Joined.somePath (PathConnectedSpace.joined (x i) q)) hx

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem subsingleton_fundamentalGroup_associatedFactor (hsum : E.componentConnectedSumDecomposition)
    (C : ConnectedComponents M.Carrier) {p : (M.component C).Carrier}
    (hsc : Subsingleton (FundamentalGroup (M.component C).Carrier p))
    (x : E.tubes.core) (hxC : ConnectedComponents.mk x.1 = C)
    (q : (E.associatedFactor x).Carrier) :
    Subsingleton (FundamentalGroup (E.associatedFactor x).Carrier q) := by
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, -, -, ⟨ρ⟩⟩ := hsum C L hL
  have hFmem : E.associatedFactor x ∈ L := hL.2.2 _ ⟨x, hxC, rfl⟩
  let y : (finiteConnectedSum (L ++ K)).Carrier := ρ.1 p
  have he := fundamentalGroupMulEquivOfHomotopyEquiv ρ.1.toHomeomorph.toHomotopyEquiv p y rfl
  have hsumSub : Subsingleton (FundamentalGroup (finiteConnectedSum (L ++ K)).Carrier y) :=
    @Equiv.subsingleton _ _ he.toEquiv.symm hsc
  exact subsingleton_fundamentalGroup_factor_of_subsingleton_finiteConnectedSum (L ++ K) _
    (List.mem_append_left _ hFmem) (fun _ => Classical.choice inferInstance) y hsumSub q

theorem subsingleton_fundamentalGroup_discardedComponent
    (hsum : E.componentConnectedSumDecomposition)
    (C : ConnectedComponents M.Carrier) {p : (M.component C).Carrier}
    (hsc : Subsingleton (FundamentalGroup (M.component C).Carrier p))
    (x : E.tubes.core) (d : E.discarded.Carrier) (hxC : ConnectedComponents.mk x.1 = C)
    (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d)
    (q : (E.outgoingFactor (Sum.inr d)).Carrier) :
    Subsingleton (FundamentalGroup (E.outgoingFactor (Sum.inr d)).Carrier q) := by
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, -, -, ⟨ρ⟩⟩ := hsum C L hL
  have hFmem : E.discarded.component (ConnectedComponents.mk d) ∈ L :=
    hL.2.2 _ ⟨x, hxC, E.associatedFactor_eq_of_presentation_eq_inr x d hd⟩
  let y : (finiteConnectedSum (L ++ K)).Carrier := ρ.1 p
  have he := fundamentalGroupMulEquivOfHomotopyEquiv ρ.1.toHomeomorph.toHomotopyEquiv p y rfl
  have hsumSub : Subsingleton (FundamentalGroup (finiteConnectedSum (L ++ K)).Carrier y) :=
    @Equiv.subsingleton _ _ he.toEquiv.symm hsc
  exact subsingleton_fundamentalGroup_factor_of_subsingleton_finiteConnectedSum (L ++ K) _
    (List.mem_append_left _ hFmem) (fun _ => Classical.choice inferInstance) y hsumSub q

theorem isPoincareStandard_discardedComponent_of_simplyConnected
    (h : simplyConnectedPoincareStandard.{u}) (hsum : E.componentConnectedSumDecomposition)
    (C : ConnectedComponents M.Carrier) {p : (M.component C).Carrier}
    (hsc : Subsingleton (FundamentalGroup (M.component C).Carrier p))
    (x : E.tubes.core) (d : E.discarded.Carrier) (hxC : ConnectedComponents.mk x.1 = C)
    (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d) :
    isPoincareStandard (E.outgoingFactor (Sum.inr d)).Carrier := by
  refine @h _ _ _ _ _ _ _ ?_
  refine simply_connected_iff_loops_nullhomotopic.mpr ⟨inferInstance, fun q γ => ?_⟩
  refine Quotient.exact
    (@Subsingleton.elim _
      (E.subsingleton_fundamentalGroup_discardedComponent hsum C hsc x d hxC hd q) _ _)

end SphericalCutCapTransition

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def discardedSideStandardRealization (T : RetainedCoreObservationTower P g) : Prop :=
  ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
    DiscardedSideStandardRealization
      ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold

theorem hasPoincareStandardDiscarded_of_discardedSideStandardRealization
    (T : RetainedCoreObservationTower P g) (h : T.discardedSideStandardRealization) :
    T.hasPoincareStandardDiscarded :=
  fun n j =>
    MetricCutCapEvent.poincareStandardDiscarded_of_discardedSideStandardRealization _ (h n j)

theorem discardedSideStandardRealization_empty
    (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier] (g : P.Metric) :
    (RetainedCoreObservationTower.empty P g).discardedSideStandardRealization :=
  fun n j => Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)

end RetainedCoreObservationTower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
