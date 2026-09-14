import DifferentialGeometry.Topology.ThreeManifold.MarkedBallTubeProducer
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalGraphSumRealizationReduction

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

local instance cutCapBridgeClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance cutCapBridgeClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private theorem closedCell_three_preconnectedSpace : PreconnectedSpace (ClosedCell 3) := by
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ))
  exact Subtype.preconnectedSpace hconv.isPreconnected

private theorem exists_isOpen_pairwiseDisjoint_of_isCompact
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]
    {K : ι → Set X} (hK : ∀ i, IsCompact (K i)) (hd : Pairwise (Disjoint on K)) :
    ∃ U : ι → Set X, (∀ i, K i ⊆ U i) ∧ (∀ i, IsOpen (U i)) ∧
      Pairwise (Disjoint on U) := by
  have hdp : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (K i) (K j) := hd
  have hsep : ∀ i, ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ K i ⊆ U ∧
      (⋃ j : {j : ι // j ≠ i}, K j.1) ⊆ V ∧ Disjoint U V := by
    intro i
    have hdisj : Disjoint (K i) (⋃ j : {j : ι // j ≠ i}, K j.1) :=
      disjoint_iUnion_right.mpr fun j => hdp j.2.symm
    exact SeparatedNhds.of_isCompact_isCompact (hK i)
      (isCompact_iUnion fun j => hK j.1) hdisj
  choose U V hUo hVo hKU hKV hUV using hsep
  refine ⟨fun i => U i ∩ ⋂ j : {j : ι // j ≠ i}, V j.1, ?_, ?_, ?_⟩
  · intro i y hy
    refine ⟨hKU i hy, Set.mem_iInter.mpr fun j => hKV j.1 ?_⟩
    exact Set.mem_iUnion.mpr ⟨⟨i, Ne.symm j.2⟩, hy⟩
  · intro i
    exact (hUo i).inter (isOpen_iInter_of_finite fun j => hVo j.1)
  · intro i j hij
    simp only [onFun]
    exact (hUV i).mono Set.inter_subset_left
      (Set.inter_subset_right.trans (Set.iInter_subset _ ⟨i, hij⟩))

private theorem mem_transport_collar {E' : ClosedOrientedManifold.{u} 3}
    {c c' : ConnectedComponents E'.Carrier} (h : c = c')
    {S : Set E'.Carrier} {x : (E'.component c').Carrier} :
    (x ∈ h ▸ {y : (E'.component c).Carrier | y.val ∈ S}) ↔ x.val ∈ S := by
  cases h
  exact Iff.rfl

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

structure CutCapCollarFamily where
  collar : E.tubes.Boundary → Set E.capped.Carrier
  collar_isOpen : ∀ b, IsOpen (collar b)
  capRange_subset_collar : ∀ b, range (E.capping.cap b) ⊆ collar b
  collarBudget : E.tubes.Boundary → ℝ
  collarBudget_pos : ∀ b, 0 < collarBudget b
  collar_pairwiseDisjoint : Pairwise (Disjoint on collar)

theorem nonempty_cutCapCollarFamily : Nonempty E.CutCapCollarFamily := by
  choose U hKU hUo hUd using exists_isOpen_pairwiseDisjoint_of_isCompact
    (K := fun b : E.tubes.Boundary => range (E.capping.cap b))
    (fun b => isCompact_range (E.capping.cap b).continuous)
    (fun b b' hbb' => E.capping.cap_disjoint hbb')
  exact ⟨{ collar := U
           collar_isOpen := hUo
           capRange_subset_collar := hKU
           collarBudget := fun _ => 1
           collarBudget_pos := fun _ => one_pos
           collar_pairwiseDisjoint := hUd }⟩

noncomputable def cutCapVertex (a : E.tubes.Index) (side : Bool) :
    ConnectedComponents E.capped.Carrier :=
  ConnectedComponents.mk
    (E.capping.coreInclusion (E.tubes.coreBoundarySphere (a, side) sphereBasePoint))

theorem capRange_subset_componentSet (a : E.tubes.Index) (side : Bool) :
    range (E.capping.cap (a, side)) ⊆
      ClosedOrientedManifold.componentSet E.capped (E.cutCapVertex a side) := by
  let _ : PreconnectedSpace (ClosedCell 3) := closedCell_three_preconnectedSpace
  have hpre : IsPreconnected (range (E.capping.cap (a, side))) :=
    isPreconnected_range (E.capping.cap (a, side)).continuous
  have hcore : IsPreconnected
      (range fun z : S2 => E.capping.coreInclusion (E.tubes.coreBoundarySphere (a, side) z)) :=
    isPreconnected_range (E.capping.coreInclusion.continuous.comp
      (E.tubes.coreBoundarySphere (a, side)).continuous)
  have hpt : E.capping.coreInclusion
      (E.tubes.coreBoundarySphere (a, side) (E.capping.attaching (a, side) sphereBasePoint)) ∈
      range fun z : S2 => E.capping.coreInclusion (E.tubes.coreBoundarySphere (a, side) z) :=
    ⟨_, rfl⟩
  have hone : ConnectedComponents.mk
      (E.capping.coreInclusion (E.tubes.coreBoundarySphere (a, side)
        (E.capping.attaching (a, side) sphereBasePoint))) = E.cutCapVertex a side :=
    ConnectedComponents.coe_eq_coe'.mpr
      (hcore.subset_connectedComponent ⟨sphereBasePoint, rfl⟩ hpt)
  have hmem : ConnectedComponents.mk
      (E.capping.cap (a, side) (sphereToClosedCell sphereBasePoint)) = E.cutCapVertex a side := by
    rw [E.capping.boundary_eq (a, side) sphereBasePoint]
    exact hone
  intro y hy
  rw [ClosedOrientedManifold.mem_componentSet]
  exact (ConnectedComponents.coe_eq_coe'.mpr
    (hpre.subset_connectedComponent ⟨_, rfl⟩ hy)).trans hmem

noncomputable def cutCapFlag (K : E.CutCapCollarFamily) (a : E.tubes.Index) (side : Bool) :
    MarkedBall (E.capped.component (E.cutCapVertex a side)).toClosedOrientedManifold where
  ball := fun x => ⟨E.capping.cap (a, side) x,
    E.capRange_subset_componentSet a side ⟨x, rfl⟩⟩
  ball_embedding := by
    refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡∂ 3) (𝓡 3)
      (E.capped.componentOpen (E.cutCapVertex a side)) _ ?_
    exact E.capping.cap_embedding (a, side)
  collar := {y | y.val ∈ K.collar (a, side)}
  collar_isOpen :=
    isOpen_induced_iff.mpr ⟨K.collar (a, side), K.collar_isOpen (a, side), rfl⟩
  ball_subset_collar := by
    rintro y ⟨x, rfl⟩
    exact K.capRange_subset_collar (a, side) ⟨x, rfl⟩
  collarBudget := K.collarBudget (a, side)
  collarBudget_pos := K.collarBudget_pos (a, side)

theorem cutCapFlag_collar_eq (K : E.CutCapCollarFamily) (a : E.tubes.Index) (side : Bool) :
    (E.cutCapFlag K a side).collar =
      {y : (E.capped.component (E.cutCapVertex a side)).Carrier |
        y.val ∈ K.collar (a, side)} := rfl

theorem cutCapFlag_collar_pairwiseDisjoint (K : E.CutCapCollarFamily) :
    ∀ (v : ConnectedComponents E.capped.Carrier)
      (f f' : {p : ULift.{u, 0} E.tubes.Index × Bool //
        E.cutCapVertex p.1.down p.2 = v}), f ≠ f' →
      Disjoint (f.2 ▸ (E.cutCapFlag K f.1.1.down f.1.2).collar)
        (f'.2 ▸ (E.cutCapFlag K f'.1.1.down f'.1.2).collar) := by
  rintro v ⟨⟨a, side⟩, hv⟩ ⟨⟨a', side'⟩, hv'⟩ hne
  have hb : (a, side) ≠ (a', side') := fun h => hne (Subtype.ext h)
  have hbd : (a.down, side) ≠ (a'.down, side') := fun h => by
    have h1 : a = a' := ULift.down_injective (congrArg Prod.fst h)
    have h2 : side = side' := congrArg Prod.snd h
    exact hb (Prod.ext h1 h2)
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  rw [cutCapFlag_collar_eq, mem_transport_collar] at hx
  rw [cutCapFlag_collar_eq, mem_transport_collar] at hx'
  exact Set.disjoint_left.mp (K.collar_pairwiseDisjoint hbd) hx hx'

noncomputable def cutCapMarkedGraph (K : E.CutCapCollarFamily) : MarkedManifoldGraph.{u} where
  Vertex := ConnectedComponents E.capped.Carrier
  Edge := ULift.{u, 0} E.tubes.Index
  vertexFintype := @Fintype.ofFinite _ (ClosedOrientedManifold.finite_components E.capped)
  edgeFintype := inferInstance
  edgeDecidableEq := Classical.decEq _
  endpoint := fun a side => E.cutCapVertex a.down side
  vertexManifold := fun v => E.capped.component v
  flag := fun a side => E.cutCapFlag K a.down side
  flag_collar_disjoint := E.cutCapFlag_collar_pairwiseDisjoint K
  attach := fun a side z => ⟨E.capping.cap (a.down, side) (sphereToClosedCell z),
    E.capRange_subset_componentSet a.down side ⟨_, rfl⟩⟩
  attach_eq := fun _ _ _ => rfl

theorem cutCapMarkedGraph_Vertex (K : E.CutCapCollarFamily) :
    (E.cutCapMarkedGraph K).Vertex = ConnectedComponents E.capped.Carrier := rfl

theorem cutCapMarkedGraph_Edge (K : E.CutCapCollarFamily) :
    (E.cutCapMarkedGraph K).Edge = ULift.{u, 0} E.tubes.Index := rfl

theorem cutCapMarkedGraph_endpoint (K : E.CutCapCollarFamily)
    (a : ULift.{u, 0} E.tubes.Index) (side : Bool) :
    (E.cutCapMarkedGraph K).endpoint a side = E.cutCapVertex a.down side := rfl

theorem cutCapMarkedGraph_vertexManifold (K : E.CutCapCollarFamily)
    (v : ConnectedComponents E.capped.Carrier) :
    (E.cutCapMarkedGraph K).vertexManifold v = E.capped.component v := rfl

theorem cutCapMarkedGraph_flag_ball (K : E.CutCapCollarFamily)
    (a : ULift.{u, 0} E.tubes.Index) (side : Bool) (x : ClosedCell 3) :
    ((E.cutCapMarkedGraph K).flag a side).ball x =
      ⟨E.capping.cap (a.down, side) x,
        E.capRange_subset_componentSet a.down side ⟨x, rfl⟩⟩ := rfl

theorem cutCapMarkedGraph_attach (K : E.CutCapCollarFamily)
    (a : ULift.{u, 0} E.tubes.Index) (side : Bool) (z : S2) :
    (E.cutCapMarkedGraph K).attach a side z =
      ⟨E.capping.cap (a.down, side) (sphereToClosedCell z),
        E.capRange_subset_componentSet a.down side ⟨_, rfl⟩⟩ := rfl

theorem cutCapMarkedGraph_vertexBlockList_eq (K : E.CutCapCollarFamily)
    (S : Finset (ULift.{u, 0} E.tubes.Index)) (v : ConnectedComponents E.capped.Carrier) :
    (E.cutCapMarkedGraph K).vertexBlockList S v =
      ((E.cutCapMarkedGraph K).vertexBlock S v).toList.map
        (fun w => E.capped.component w) := rfl

theorem removedBallSet_empty_cutCapMarkedGraph (K : E.CutCapCollarFamily)
    (v : ConnectedComponents E.capped.Carrier) :
    (E.cutCapMarkedGraph K).removedBallSet
      (∅ : Finset (ULift.{u, 0} E.tubes.Index)) v = ∅ :=
  MarkedManifoldGraph.removedBallSet_empty (G := E.cutCapMarkedGraph K) v

noncomputable def cutCapEmptyRealization (K : E.CutCapCollarFamily) :
    PartialRealization (E.cutCapMarkedGraph K)
      (∅ : Finset (ULift.{u, 0} E.tubes.Index)) where
  realization := E.capped
  vertexPiece := fun _ => ⟨fun y => y.1.val, continuous_subtype_val.comp continuous_subtype_val⟩
  cylinderPiece := fun e he => ((Finset.notMem_empty e) he).elim
  survivingFlag := fun e _ =>
    { ball := E.capping.cap (e.down, false)
      ball_embedding := E.capping.cap_embedding (e.down, false)
      collar := K.collar (e.down, false)
      collar_isOpen := K.collar_isOpen (e.down, false)
      ball_subset_collar := K.capRange_subset_collar (e.down, false)
      collarBudget := K.collarBudget (e.down, false)
      collarBudget_pos := K.collarBudget_pos (e.down, false) }
  covers := fun x => by
    let hx : E.capped.Carrier := x
    have hmem : (⟨hx, rfl⟩ : E.capped.componentSet (ConnectedComponents.mk hx)) ∉
        (E.cutCapMarkedGraph K).removedBallSet
          (∅ : Finset (ULift.{u, 0} E.tubes.Index)) (ConnectedComponents.mk hx) := by
      rw [removedBallSet_empty_cutCapMarkedGraph]
      exact Set.notMem_empty _
    exact Or.inl ⟨ConnectedComponents.mk hx, ⟨⟨⟨hx, rfl⟩, hmem⟩, rfl⟩⟩
  survivingFlag_collar_disjoint := fun e e' _ _ hne =>
    K.collar_pairwiseDisjoint fun h =>
      hne (ULift.down_injective (congrArg Prod.fst h))

theorem cutCapEmptyRealization_componentCorrespondence (K : E.CutCapCollarFamily) :
    (E.cutCapEmptyRealization K).componentCorrespondence := by
  intro v v' y y'
  rw [show (E.cutCapMarkedGraph K).processedGraph (∅ : Finset (ULift.{u, 0} E.tubes.Index)) =
    ⊥ from Finset.sup_empty, SimpleGraph.reachable_bot]
  constructor
  · intro h
    change ConnectedComponents.mk y.1.val = ConnectedComponents.mk y'.1.val at h
    exact y.1.2.symm.trans (h.trans y'.1.2)
  · intro h
    subst h
    exact y.1.2.trans y'.1.2.symm

theorem cutCapEmptyRealization_hasBlockPresentation (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    (E.cutCapEmptyRealization K).HasBlockPresentation S := by
  refine ⟨fun _ => 0, fun _ _ _ => rfl, fun v y => ?_⟩
  change Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
    (E.capped.component (ConnectedComponents.mk y.1.val)).toClosedOrientedManifold
    (finiteConnectedSum ((E.cutCapMarkedGraph K).vertexBlockList ∅ v ++
      List.replicate 0 S)).toClosedOrientedManifold)
  rw [MarkedManifoldGraph.vertexBlockList_empty]
  simp only [List.replicate_zero, List.append_nil, finiteConnectedSum_singleton]
  rw [y.1.2]
  exact ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

theorem cutCapEmptyRealization_cylinderComponentCovering (K : E.CutCapCollarFamily) :
    (E.cutCapEmptyRealization K).CylinderComponentCovering := by
  intro x
  let hx : E.capped.Carrier := x
  have hmem : (⟨hx, rfl⟩ : E.capped.componentSet (ConnectedComponents.mk hx)) ∉
      (E.cutCapMarkedGraph K).removedBallSet
        (∅ : Finset (ULift.{u, 0} E.tubes.Index)) (ConnectedComponents.mk hx) := by
    rw [removedBallSet_empty_cutCapMarkedGraph]
    exact Set.notMem_empty _
  exact ⟨ConnectedComponents.mk hx, ⟨⟨⟨hx, rfl⟩, hmem⟩, rfl⟩⟩

theorem cutCapEmptyRealization_isBlockInvariant (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    (E.cutCapEmptyRealization K).IsBlockInvariant S :=
  ⟨E.cutCapEmptyRealization_componentCorrespondence K,
    E.cutCapEmptyRealization_hasBlockPresentation K S,
    E.cutCapEmptyRealization_cylinderComponentCovering K⟩

theorem exists_cutCapEmptyRealization_blockInvariant (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ P : PartialRealization (E.cutCapMarkedGraph K)
      (∅ : Finset (ULift.{u, 0} E.tubes.Index)), P.IsBlockInvariant S :=
  ⟨E.cutCapEmptyRealization K, E.cutCapEmptyRealization_isBlockInvariant K S⟩

theorem cutCapMarkedGraph_flag (K : E.CutCapCollarFamily)
    (a : ULift.{u, 0} E.tubes.Index) (side : Bool) :
    (E.cutCapMarkedGraph K).flag a side = E.cutCapFlag K a.down side := rfl

theorem cutCapMarkedGraph_flag_collar (K : E.CutCapCollarFamily)
    (a : ULift.{u, 0} E.tubes.Index) (side : Bool) :
    ((E.cutCapMarkedGraph K).flag a side).collar =
      {y : (E.capped.component (E.cutCapVertex a.down side)).Carrier |
        y.val ∈ K.collar (a.down, side)} := rfl

noncomputable def cutCapEdgeFinset (T : Finset E.tubes.Index) :
    Finset (ULift.{u, 0} E.tubes.Index) :=
  T.map ⟨ULift.up, fun _ _ h => ULift.down_inj.mpr h⟩

theorem mem_cutCapEdgeFinset (T : Finset E.tubes.Index) (a : E.tubes.Index) :
    ULift.up a ∈ E.cutCapEdgeFinset T ↔ a ∈ T := by
  classical
  rw [cutCapEdgeFinset, Finset.mem_map]
  exact ⟨fun ⟨b, hb, hba⟩ => by cases hba; exact hb, fun ha => ⟨a, ha, rfl⟩⟩

theorem cutCapEdgeFinset_card (T : Finset E.tubes.Index) :
    (E.cutCapEdgeFinset T).card = T.card :=
  Finset.card_map _

structure CutCapGraphRealization (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) where
  realization : PartialRealization (E.cutCapMarkedGraph K) Finset.univ
  blockInvariant : realization.IsBlockInvariant S
  source_component : ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∃ (v : (E.cutCapMarkedGraph K).Vertex)
      (y : (E.cutCapMarkedGraph K).puncturedCarrier Finset.univ v),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (realization.realization.component
          (ConnectedComponents.mk (realization.vertexPiece v y))).toClosedOrientedManifold) ∧
      List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
          B.toClosedOrientedManifold))
        ((E.cutCapMarkedGraph K).vertexBlockList Finset.univ v) (E.cappedCutPieceFactorList C)

theorem componentPresentationData_of_cutCapGraphRealization (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.CutCapGraphRealization K S) :
    E.ComponentPresentationData S := by
  intro C hC
  obtain ⟨v, y, hcomp, hpieces⟩ := h.source_component C hC
  obtain ⟨b, _, hb⟩ := h.blockInvariant.2.1
  exact ⟨(E.cutCapMarkedGraph K).vertexBlockList Finset.univ v, b v, hpieces,
    hcomp.map fun ρ => ρ.trans (hb v y).some⟩

theorem sphericalSummandCompletion_of_cutCapGraphRealization (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.CutCapGraphRealization K S) :
    E.sphericalSummandCompletion S :=
  E.sphericalSummandCompletion_of_componentPresentationData S
    (E.componentPresentationData_of_cutCapGraphRealization K S h)

theorem blockStepLaw_of_isEmpty_index (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) [IsEmpty E.tubes.Index] :
    BlockStepLaw (E.cutCapMarkedGraph K) S := by
  have hEdge : IsEmpty (E.cutCapMarkedGraph K).Edge :=
    ⟨fun e => isEmptyElim (e : ULift.{u, 0} E.tubes.Index).down⟩
  exact blockStepLaw_of_hasRealizationStep_of_initial
    (E.exists_cutCapEmptyRealization_blockInvariant K S)
    (fun _ _ e _ _ => isEmptyElim e)

theorem sphericalSummandCompletion_of_isEmpty_index (S : ConnectedClosedOrientedManifold.{u} 3)
    [IsEmpty E.tubes.Index] : E.sphericalSummandCompletion S :=
  E.sphericalSummandCompletion_of_componentPresentationData S
    (E.componentPresentationData_of_forall_cutIndices_eq_empty S
      fun C => E.cutIndices_eq_empty_of_isEmpty_index C)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
