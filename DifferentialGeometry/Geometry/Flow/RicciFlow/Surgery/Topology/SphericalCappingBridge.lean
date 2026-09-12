import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidence

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
local instance : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

namespace SphericalTubeSystem

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

@[reducible] def toTopological :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem M.Carrier where
  Index := T.Index
  finiteIndex := T.finiteIndex
  tube := T.tube
  embedding := fun a => (T.smooth a).isEmbedding
  disjoint := T.disjoint

theorem toTopological_core : T.toTopological.core = T.core := rfl

theorem toTopological_boundarySphere (b : T.Boundary) :
    T.toTopological.boundarySphere b = T.boundarySphere b := rfl

theorem toTopological_coreBoundarySphere (b : T.Boundary) :
    T.toTopological.coreBoundarySphere b = T.coreBoundarySphere b := rfl

end SphericalTubeSystem

namespace SphericalCapping

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}

private def ballHomeomorph :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeBall ≃ₜ ClosedCell 3 :=
  (Handle.closedCellBallHomeo 3).symm

private theorem ballHomeomorph_sphereToThreeBall
    (y : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2) :
    ballHomeomorph (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereToThreeBall y) =
      sphereToClosedCell y :=
  Subtype.ext rfl

variable (K : SphericalCapping M N T)

private def capMap (b : T.Boundary) :
    C(DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeBall, N.Carrier) :=
  (K.cap b).comp ⟨ballHomeomorph, ballHomeomorph.continuous_toFun⟩

private theorem capMap_coe (b : T.Boundary) :
    ⇑(K.capMap b) = ⇑(K.cap b) ∘ ⇑ballHomeomorph := rfl

private theorem range_capMap (b : T.Boundary) :
    Set.range ⇑(K.capMap b) = Set.range ⇑(K.cap b) := by
  rw [capMap_coe, Set.range_comp, ballHomeomorph.surjective.range_eq, Set.image_univ]

private theorem iUnion_range_capMap :
    (⋃ b, Set.range ⇑(K.capMap b)) = ⋃ b, Set.range ⇑(K.cap b) :=
  iUnion_congr fun b => range_capMap K b

noncomputable def toTopological :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping T.toTopological N.Carrier := by
  letI := K.coreCharts
  letI := K.coreSmooth
  exact
  { coreInclusion := K.coreInclusion
    coreEmbedding := K.core_embedding.isEmbedding
    cap := K.capMap
    capEmbedding := fun b =>
      (K.cap_embedding b).isEmbedding.comp ballHomeomorph.isEmbedding
    attaching := fun b => (K.attaching b).toHomeomorph
    boundary_eq := fun b y =>
      (congrArg (fun p => K.cap b p) (ballHomeomorph_sphereToThreeBall y)).trans
        (K.boundary_eq b y)
    exhaustive :=
      (congrArg (fun s => Set.range ⇑K.coreInclusion ∪ s)
        (iUnion_range_capMap K)).trans K.exhaustive
    core_cap_intersection := fun b =>
      (congrArg (fun s => Set.range ⇑K.coreInclusion ∩ s)
        (range_capMap K b)).trans (K.core_cap_intersection b)
    cap_disjoint := fun b b' hne =>
      (K.cap_disjoint hne).mono (range_capMap K b).subset
        (range_capMap K b').subset }

theorem toTopological_coreInclusion (x : T.core) :
    K.toTopological.coreInclusion x = K.coreInclusion x := rfl

theorem range_toTopological_cap (b : T.Boundary) :
    Set.range ⇑(K.toTopological.cap b) = Set.range ⇑(K.cap b) :=
  range_capMap K b

theorem iUnion_range_toTopological_cap :
    (⋃ b, Set.range ⇑(K.toTopological.cap b)) = ⋃ b, Set.range ⇑(K.cap b) :=
  iUnion_range_capMap K

def componentMap : ConnectedComponents T.core → ConnectedComponents N.Carrier :=
  K.coreInclusion.continuous.connectedComponentsMap

theorem componentMap_mk (x : T.core) :
    K.componentMap (ConnectedComponents.mk x) =
      ConnectedComponents.mk (K.coreInclusion x) := rfl

theorem rfs_cap_component_bijection [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [T2Space N.Carrier] : Function.Bijective K.componentMap := by
  let _ : CompactSpace T.toTopological.core := isCompact_iff_compactSpace.mp K.core_compact
  let _ : LocallyConnectedSpace T.toTopological.core :=
    K.coreCharts.locallyConnectedSpace (EuclideanHalfSpace 3) T.core
  exact DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.rfs_cap_component_bijection
    K.toTopological

noncomputable def componentEquiv [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [T2Space N.Carrier] :
    ConnectedComponents T.core ≃ ConnectedComponents N.Carrier :=
  Equiv.ofBijective K.componentMap (K.rfs_cap_component_bijection)

theorem componentEquiv_apply [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [T2Space N.Carrier] (x : T.core) :
    K.componentEquiv (ConnectedComponents.mk x) =
      ConnectedComponents.mk (K.coreInclusion x) := rfl

theorem component_meets_core [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [T2Space N.Carrier] (c : ConnectedComponents N.Carrier) :
    ∃ x : T.core, ConnectedComponents.mk (K.coreInclusion x) = c := by
  obtain ⟨d, hd⟩ := (K.rfs_cap_component_bijection).surjective c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe d
  exact ⟨x, hd⟩

end SphericalCapping

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

noncomputable def toTopological :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology
      M.Carrier Q.Carrier E.discarded.Carrier E.capped.Carrier where
  tubes := E.tubes.toTopological
  capping := E.capping.toTopological
  presentation := E.presentation.toHomeomorph
  nontrivial := E.nontrivial

theorem toTopological_tubes :
    E.toTopological.tubes = E.tubes.toTopological := rfl

theorem toTopological_presentation (x : E.capped.Carrier) :
    E.toTopological.presentation x = E.presentation x := rfl

def coreCutComponents (C : ConnectedComponents M.Carrier) :
    Set (ConnectedComponents E.tubes.core) :=
  {d | continuous_subtype_val.connectedComponentsMap d = C}

theorem mem_coreCutComponents_iff (C : ConnectedComponents M.Carrier)
    (d : ConnectedComponents E.tubes.core) :
    d ∈ E.coreCutComponents C ↔ continuous_subtype_val.connectedComponentsMap d = C :=
  Iff.rfl

theorem coreBoundarySphere_mem_coreCutComponents (C : ConnectedComponents M.Carrier)
    (a : E.cutIndices C) (side : Bool)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ConnectedComponents.mk (E.tubes.coreBoundarySphere (a.1, side) z) ∈
      E.coreCutComponents C := by
  rw [mem_coreCutComponents_iff, Continuous.connectedComponentsMap_mk]
  exact E.mk_coreBoundarySphere_eq C a side z

theorem coreCutComponents_nonempty (C : ConnectedComponents M.Carrier) :
    (E.coreCutComponents C).Nonempty := by
  obtain ⟨x, hx⟩ := E.exists_core_mem_componentSet C
  exact ⟨ConnectedComponents.mk x, by
    rw [mem_coreCutComponents_iff, Continuous.connectedComponentsMap_mk]
    exact hx⟩

theorem componentMap_mem_cappedCutComponents (C : ConnectedComponents M.Carrier)
    {d : ConnectedComponents E.tubes.core} (hd : d ∈ E.coreCutComponents C) :
    E.capping.componentMap d ∈ E.cappedCutComponents C := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe d
  have hxC : ConnectedComponents.mk x.1 = C := by
    have h := hd
    rw [mem_coreCutComponents_iff, ← hx, Continuous.connectedComponentsMap_mk] at h
    exact h
  refine ⟨x, hxC, ?_⟩
  rw [← hx, SphericalCapping.componentMap_mk]

noncomputable def coreToCapped (C : ConnectedComponents M.Carrier)
    (d : E.coreCutComponents C) : E.cappedCutComponents C :=
  ⟨E.capping.componentMap d.1, E.componentMap_mem_cappedCutComponents C d.2⟩

theorem coreToCapped_injective (C : ConnectedComponents M.Carrier)
    [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core] :
    Function.Injective (E.coreToCapped C) := by
  intro d d' h
  refine Subtype.ext ((E.capping.rfs_cap_component_bijection).injective ?_)
  exact congrArg Subtype.val h

theorem coreToCapped_surjective (C : ConnectedComponents M.Carrier) :
    Function.Surjective (E.coreToCapped C) := by
  intro D
  obtain ⟨x, hxC, hxD⟩ := D.2
  refine ⟨⟨ConnectedComponents.mk x, ?_⟩, ?_⟩
  · rw [mem_coreCutComponents_iff, Continuous.connectedComponentsMap_mk]
    exact hxC
  · refine Subtype.ext ?_
    simp only [coreToCapped]
    rw [SphericalCapping.componentMap_mk]
    exact hxD

theorem coreToCapped_bijective (C : ConnectedComponents M.Carrier)
    [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core] :
    Function.Bijective (E.coreToCapped C) :=
  ⟨E.coreToCapped_injective C, E.coreToCapped_surjective C⟩

theorem cappedCutComponents_nonempty (C : ConnectedComponents M.Carrier) :
    (E.cappedCutComponents C).Nonempty := by
  obtain ⟨d, hd⟩ := E.coreCutComponents_nonempty C
  exact ⟨E.coreToCapped C ⟨d, hd⟩, (E.coreToCapped C ⟨d, hd⟩).2⟩

theorem natCard_coreCutComponents_eq_cappedCutComponents (C : ConnectedComponents M.Carrier)
    [CompactSpace E.tubes.core] [LocallyConnectedSpace E.tubes.core] :
    Nat.card (E.coreCutComponents C) = Nat.card (E.cappedCutComponents C) :=
  Nat.card_eq_of_bijective _ (E.coreToCapped_bijective C)

theorem cappedCutComponents_finite (C : ConnectedComponents M.Carrier) :
    (E.cappedCutComponents C).Finite := by
  let _ : Finite (ConnectedComponents E.capped.Carrier) :=
    DifferentialGeometry.Topology.ClosedOrientedManifold.finite_components E.capped
  exact Set.toFinite _

theorem ncard_associatedFactors_le_natCard_cappedCutComponents
    (C : ConnectedComponents M.Carrier) :
    (E.associatedFactors C).ncard ≤ Nat.card (E.cappedCutComponents C) := by
  let _ : Finite (E.cappedCutComponents C) := by
    let _ : Finite (ConnectedComponents E.capped.Carrier) :=
      DifferentialGeometry.Topology.ClosedOrientedManifold.finite_components E.capped
    infer_instance
  rw [E.associatedFactors_eq_range_cappedFactor, ← Set.image_univ]
  have h := Set.ncard_image_le (s := (Set.univ : Set (E.cappedCutComponents C)))
    (f := E.cappedFactor C) (Set.toFinite _)
  rwa [Set.ncard_univ] at h

end SphericalCutCapTransition

end DifferentialGeometry.Topology
