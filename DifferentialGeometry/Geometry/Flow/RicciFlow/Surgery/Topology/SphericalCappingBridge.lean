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

theorem rfs_cap_component_bijection
    [T2Space N.Carrier] : Function.Bijective K.componentMap := by
  let _ : CompactSpace T.toTopological.core := isCompact_iff_compactSpace.mp K.core_compact
  let _ : LocallyConnectedSpace T.toTopological.core :=
    K.coreCharts.locallyConnectedSpace (EuclideanHalfSpace 3) T.core
  exact DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.rfs_cap_component_bijection
    K.toTopological

noncomputable def componentEquiv
    [T2Space N.Carrier] :
    ConnectedComponents T.core ≃ ConnectedComponents N.Carrier :=
  Equiv.ofBijective K.componentMap (K.rfs_cap_component_bijection)

theorem componentEquiv_apply
    [T2Space N.Carrier] (x : T.core) :
    K.componentEquiv (ConnectedComponents.mk x) =
      ConnectedComponents.mk (K.coreInclusion x) := rfl

theorem component_meets_core
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

theorem coreToCapped_injective (C : ConnectedComponents M.Carrier) :
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

theorem coreToCapped_bijective (C : ConnectedComponents M.Carrier) :
    Function.Bijective (E.coreToCapped C) :=
  ⟨E.coreToCapped_injective C, E.coreToCapped_surjective C⟩

theorem cappedCutComponents_nonempty (C : ConnectedComponents M.Carrier) :
    (E.cappedCutComponents C).Nonempty := by
  obtain ⟨d, hd⟩ := E.coreCutComponents_nonempty C
  exact ⟨E.coreToCapped C ⟨d, hd⟩, (E.coreToCapped C ⟨d, hd⟩).2⟩

theorem natCard_coreCutComponents_eq_cappedCutComponents (C : ConnectedComponents M.Carrier) :
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

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem cap_mem_connectedComponent_boundary (b : T.Boundary)
    (z : ClosedCell 3) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    C.cap b z ∈ connectedComponent
      (C.coreInclusion (T.coreBoundarySphere b (C.attaching b q))) := by
  let _ : PreconnectedSpace (ClosedCell 3) := by
    have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} : Set _) := by
      simpa only [Metric.closedBall, dist_zero_right] using
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ))
    exact Subtype.preconnectedSpace hconv.isPreconnected
  have hconn : IsPreconnected (range (C.cap b)) := by
    apply isPreconnected_range
    exact (C.cap b).continuous
  have hbase : C.coreInclusion (T.coreBoundarySphere b (C.attaching b q)) ∈
      range (C.cap b) := ⟨sphereToClosedCell q, C.boundary_eq b q⟩
  exact hconn.subset_connectedComponent hbase (mem_range_self z)

theorem image_coreComponent_union_caps_eq_connectedComponent
    (x : T.core) (B : Set T.Boundary)
    (hboundary : ∀ b ∈ B, ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      T.coreBoundarySphere b z ∈ connectedComponent x)
    (hexact : ∀ b : T.Boundary,
      (∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, T.coreBoundarySphere b z ∈ connectedComponent x) → b ∈ B) :
    C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ B, range (C.cap b) =
      connectedComponent (C.coreInclusion x) := by
  let _ : CompactSpace T.core := isCompact_iff_compactSpace.mp C.core_compact
  let _ : LocallyConnectedSpace T.core :=
    C.coreCharts.locallyConnectedSpace (EuclideanHalfSpace 3) T.core
  let q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hcore (y : T.core) :
      C.coreInclusion y ∈ connectedComponent (C.coreInclusion x) ↔
        y ∈ connectedComponent x := by
    constructor
    · intro hy
      apply ConnectedComponents.coe_eq_coe'.mp
      apply C.rfs_cap_component_bijection.injective
      exact ConnectedComponents.coe_eq_coe'.mpr hy
    · intro hy
      exact C.coreInclusion.continuous.mapsTo_connectedComponent x hy
  apply Subset.antisymm
  · rintro y (⟨z, hz, rfl⟩ | hy)
    · exact (hcore z).mpr hz
    · obtain ⟨b, hb, z, rfl⟩ := mem_iUnion₂.mp hy
      have hmem := C.cap_mem_connectedComponent_boundary b z q
      have hh := (hcore _).mpr (hboundary b hb (C.attaching b q))
      exact (connectedComponent_eq hh) ▸ hmem
  · intro y hy
    have hall : y ∈ range C.coreInclusion ∪ ⋃ b, range (C.cap b) := by
      rw [C.exhaustive]
      exact mem_univ y
    rcases hall with ⟨z, rfl⟩ | hall
    · exact Or.inl ⟨z, (hcore z).mp hy, rfl⟩
    · obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hall
      have hm := C.cap_mem_connectedComponent_boundary b z q
      have he := ConnectedComponents.coe_eq_coe'.mpr hm
      have hz := ConnectedComponents.coe_eq_coe'.mpr hy
      have hc : C.coreInclusion (T.coreBoundarySphere b (C.attaching b q)) ∈
          connectedComponent (C.coreInclusion x) :=
        ConnectedComponents.coe_eq_coe'.mp (he.symm.trans hz)
      exact Or.inr (mem_iUnion₂.mpr
        ⟨b, hexact b ⟨C.attaching b q, (hcore _).mp hc⟩, mem_range_self z⟩)

theorem image_coreComponent_union_cap_eq_connectedComponent
    (x : T.core) (b : T.Boundary)
    (hboundary : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      T.coreBoundarySphere b z ∈ connectedComponent x)
    (hunique : ∀ b' : T.Boundary,
      (∃ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        T.coreBoundarySphere b' z ∈ connectedComponent x) → b' = b) :
    C.coreInclusion '' connectedComponent x ∪ range (C.cap b) =
      connectedComponent (C.coreInclusion x) := by
  simpa only [Set.biUnion_singleton] using
    C.image_coreComponent_union_caps_eq_connectedComponent x {b}
      (fun b' hb' z => Set.mem_singleton_iff.mp hb' ▸ hboundary z)
      (fun b' hb' => Set.mem_singleton_iff.mpr (hunique b' hb'))

end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_core_presentation_eq_inr_component
    (D : ConnectedComponents E.discarded.Carrier) :
    ∃ (x : E.tubes.core) (d : E.discarded.Carrier),
      ConnectedComponents.mk d = D ∧
        E.presentation (E.capping.coreInclusion x) = Sum.inr d := by
  obtain ⟨d₀,hd₀⟩ := ConnectedComponents.surjective_coe D
  let _ : CompactSpace E.tubes.core := isCompact_iff_compactSpace.mp E.capping.core_compact
  let _ : LocallyConnectedSpace E.tubes.core :=
    E.capping.coreCharts.locallyConnectedSpace (EuclideanHalfSpace 3) E.tubes.core
  obtain ⟨x,hx⟩ := E.capping.component_meets_core
    (ConnectedComponents.mk (E.presentation.symm (Sum.inr d₀)))
  have hc : ConnectedComponents.mk (E.presentation (E.capping.coreInclusion x)) =
      ConnectedComponents.mk (Sum.inr d₀ : Q.Carrier ⊕ E.discarded.Carrier) := by
    have hh := congrArg E.presentation.continuous.connectedComponentsMap hx
    simpa only [Continuous.connectedComponentsMap_mk,E.presentation.apply_symm_apply] using hh
  have hmem : E.presentation (E.capping.coreInclusion x) ∈
      connectedComponent (Sum.inr d₀ : Q.Carrier ⊕ E.discarded.Carrier) :=
    ConnectedComponents.coe_eq_coe'.mp hc
  have hsub : connectedComponent (Sum.inr d₀ : Q.Carrier ⊕ E.discarded.Carrier) ⊆
      range (@Sum.inr Q.Carrier E.discarded.Carrier) :=
    isPreconnected_connectedComponent.subset_isClopen isClopen_range_inr
      ⟨Sum.inr d₀,mem_connectedComponent,⟨d₀,rfl⟩⟩
  obtain ⟨d,hd⟩ := hsub hmem
  let r : Q.Carrier ⊕ E.discarded.Carrier → E.discarded.Carrier := Sum.elim (fun _ => d₀) id
  have hr : Continuous r := continuous_const.sumElim continuous_id
  have hdd : ConnectedComponents.mk d = ConnectedComponents.mk d₀ := by
    have hh := congrArg hr.connectedComponentsMap hc
    rw [Continuous.connectedComponentsMap_mk,Continuous.connectedComponentsMap_mk,← hd] at hh
    exact hh
  exact ⟨x,d,hdd.trans hd₀,hd.symm⟩

end DifferentialGeometry.Topology.SphericalCutCapTransition

end
