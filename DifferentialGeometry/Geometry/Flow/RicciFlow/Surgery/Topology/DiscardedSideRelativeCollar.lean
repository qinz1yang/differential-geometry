import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarLocalDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreComponents
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckCylindricalChartBridge
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarSmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapPersistence

noncomputable section

open Set Bundle Manifold Function
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

def ambientNeckMap (α : (H.event i).transition.trace.tubes.Index) :
    bufferedCylinder (G.delta α) → (H.stage i.castSucc).Carrier :=
  fun z => ((G.neck α).chart z).1

theorem ambientNeckMap_injective (α : (H.event i).transition.trace.tubes.Index) :
    Injective (G.ambientNeckMap α) := by
  intro x y hxy
  exact (G.neck α).chart_smooth.isEmbedding.injective (Subtype.ext hxy)

theorem pairwise_disjoint_ambientNeckMap :
    Pairwise fun α β => Disjoint (range (G.ambientNeckMap α))
      (range (G.ambientNeckMap β)) := by
  intro α β hne
  apply disjoint_left.mpr
  rintro p ⟨x, rfl⟩ ⟨y, he⟩
  exact disjoint_left.mp (G.buffer_disjoint hne) (mem_range_self x)
    ⟨y, Subtype.ext he⟩

theorem ambientNeckMap_isOpenEmbedding (α : (H.event i).transition.trace.tubes.Index) :
    _root_.Topology.IsOpenEmbedding (G.ambientNeckMap α) := by
  obtain ⟨V, Φ, _, hΦ, _⟩ := (G.neck α).exists_cylindricalChart
  have hchart : _root_.Topology.IsOpenEmbedding ((G.neck α).chart :
      neckBuffer (G.delta α) → (H.event i).incoming.terminalRegularOpen) := by
    have he : ((G.neck α).chart : neckBuffer (G.delta α) →
        (H.event i).incoming.terminalRegularOpen) = Subtype.val ∘ Φ := by
      funext z
      exact (hΦ z).symm
    rw [he]
    exact V.isOpen.isOpenEmbedding_subtypeVal.comp Φ.toHomeomorph.isOpenEmbedding
  exact (H.event i).incoming.terminalRegularOpen.isOpen.isOpenEmbedding_subtypeVal.comp hchart

theorem removedSlab_ambientNeckMap (α : (H.event i).transition.trace.tubes.Index) :
    removedSlab (G.ambientNeckMap α) = (H.event i).transition.trace.tubes.removedBand α := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact G.mem_removedBand_of_neckChart_abs_lt_one α z (abs_lt.mpr hz)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨(z.1, z.2.1), G.tube_in_buffer α z⟩, hz, ?_⟩
    exact (G.tube_eq α z (G.tube_in_buffer α z)).symm

theorem cutCore_ambientNeckMap :
    cutCore G.ambientNeckMap = (H.event i).transition.trace.tubes.core := by
  unfold cutCore TubeSystem.core
  simp_rw [G.removedSlab_ambientNeckMap]

def coreCollar (b : (H.event i).transition.trace.tubes.Boundary) :
    Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1)) →
      (H.event i).transition.trace.tubes.core :=
  fun q => ⟨G.ambientNeckMap b.1 (cuttingCollarCylinderMap (G.delta_pos b.1) b.2 q), by
    rw [← G.cutCore_ambientNeckMap]
    exact cuttingCollar_mem_cutCore G.delta_pos G.ambientNeckMap G.ambientNeckMap_injective
      G.pairwise_disjoint_ambientNeckMap b q⟩

theorem coreCollar_zero (b : (H.event i).transition.trace.tubes.Boundary) (y : Sphere 2) :
    G.coreCollar b (y, ⟨0, le_rfl, cuttingCollarWidth_pos (G.delta_pos b.1)⟩) =
      (H.event i).transition.trace.tubes.coreBoundarySphere b y := by
  apply Subtype.ext
  change G.ambientNeckMap b.1 (cuttingCollarCylinderMap (G.delta_pos b.1) b.2 _) =
    (H.event i).transition.trace.tubes.tube b.1 (y, TubeSystem.boundaryLevel b.2)
  rw [G.tube_eq b.1 _ (G.tube_in_buffer b.1 _)]
  apply congrArg (fun z : neckBuffer (G.delta b.1) => ((G.neck b.1).chart z).1)
  apply Subtype.ext
  rw [cuttingCollarCylinderMap_val]
  cases b.2 <;> simp [TubeSystem.boundaryLevel, cuttingSign]


theorem coreCollar_isOpenEmbedding (b : (H.event i).transition.trace.tubes.Boundary) :
    _root_.Topology.IsOpenEmbedding (G.coreCollar b) := by
  have he : G.coreCollar b = (Homeomorph.setCongr G.cutCore_ambientNeckMap) ∘
      cuttingCollarMap G.delta_pos G.ambientNeckMap G.ambientNeckMap_injective
        G.pairwise_disjoint_ambientNeckMap b := rfl
  rw [he]
  exact (Homeomorph.setCongr G.cutCore_ambientNeckMap).isOpenEmbedding.comp
    (isOpenEmbedding_cuttingCollarMap G.delta_pos G.ambientNeckMap
      G.ambientNeckMap_isOpenEmbedding G.pairwise_disjoint_ambientNeckMap b)

theorem coreCollar_contMDiff (b : (H.event i).transition.trace.tubes.Boundary) :
    let : ChartedSpace (EuclideanHalfSpace 1)
        (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
      DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace
        (cuttingCollarWidth_pos (G.delta_pos b.1))
    let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
      (H.event i).transition.coreCharts
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ (G.coreCollar b) := by
  let : ChartedSpace (EuclideanHalfSpace 1)
      (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
    DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace
      (cuttingCollarWidth_pos (G.delta_pos b.1))
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.coreCharts
  apply (ContMDiff.iff_comp_isImmersion (H.event i).transition.core_induced.isImmersion).mpr
  refine ⟨(G.coreCollar_isOpenEmbedding b).continuous, ?_⟩
  exact contMDiff_subtype_val.comp ((G.neck b.1).chart_smooth.contMDiff.comp
    (cuttingCollarCylinderMap_contMDiff (G.delta_pos b.1) b.2))

theorem coreCollar_mem_connectedComponent (b : (H.event i).transition.trace.tubes.Boundary)
    (y : Sphere 2) (q : Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :
    G.coreCollar b q ∈ connectedComponent ((H.event i).transition.trace.tubes.coreBoundarySphere b y) := by
  have : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    ((isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one).isPreconnected)
  have : PreconnectedSpace (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ico
  have hp := isPreconnected_range (G.coreCollar_isOpenEmbedding b).continuous
  exact hp.subset_connectedComponent ⟨(y, ⟨0, le_rfl, cuttingCollarWidth_pos (G.delta_pos b.1)⟩),
    G.coreCollar_zero b y⟩ (mem_range_self q)

theorem coreCollar_not_mem_retainedCore (b : (H.event i).transition.trace.tubes.Boundary)
    (y : Sphere 2) (hy : (H.event i).transition.trace.tubes.coreBoundarySphere b y ∉
      (H.event i).transition.trace.retainedCore)
    (q : Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :
    G.coreCollar b q ∉ (H.event i).transition.trace.retainedCore :=
  CutCapTopology.connectedComponent_subset_compl_retainedCore _ _ hy
    (G.coreCollar_mem_connectedComponent b y q)


theorem coreCollar_not_mem_retainedCore_of_capDiscarded
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b)
    (y : Sphere 2)
    (q : Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :
    G.coreCollar b q ∉ (H.event i).transition.trace.retainedCore :=
  G.coreCollar_not_mem_retainedCore b y
    (CutCapTopology.capDiscarded_coreBoundarySphere_not_mem_retainedCore
      (H.event i).transition.trace b hb y) q

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

def coreCollarRegion : Set (H.event i).transition.trace.tubes.core :=
  ⋃ b, range (G.coreCollar b)

theorem isOpen_coreCollarRegion : IsOpen G.coreCollarRegion :=
  isOpen_iUnion fun b => (G.coreCollar_isOpenEmbedding b).isOpen_range

theorem core_boundary_subset_coreCollarRegion :
    let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
      (H.event i).transition.coreCharts
    (𝓡∂ 3).boundary (H.event i).transition.trace.tubes.core ⊆ G.coreCollarRegion := by
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.coreCharts
  dsimp only
  rw [(H.event i).transition.core_boundary]
  rintro x hx
  obtain ⟨b, y, rfl⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨b, ⟨(y, ⟨0, le_rfl, cuttingCollarWidth_pos (G.delta_pos b.1)⟩),
    G.coreCollar_zero b y⟩⟩

theorem pairwise_disjoint_coreCollars :
    Pairwise fun b c : (H.event i).transition.trace.tubes.Boundary =>
      Disjoint (range (G.coreCollar b)) (range (G.coreCollar c)) := by
  intro b c hbc
  apply disjoint_left.mpr
  rintro p ⟨q, rfl⟩ ⟨r, hr⟩
  have hg := pairwise_disjoint_cuttingCollars G.delta_pos G.ambientNeckMap
    G.ambientNeckMap_injective G.pairwise_disjoint_ambientNeckMap hbc
  apply disjoint_left.mp hg (mem_range_self q)
  refine ⟨r, ?_⟩
  apply Subtype.ext
  exact congrArg (fun z : (H.event i).transition.trace.tubes.core => z.val) hr

theorem coreCollarRegion_compl_subset_interior :
    (Subtype.val : (H.event i).transition.trace.tubes.core → (H.stage i.castSucc).Carrier) ''
      G.coreCollarRegionᶜ ⊆ interior (H.event i).transition.trace.tubes.core := by
  rintro p ⟨x, hx, rfl⟩
  by_contra hnot
  have hxcore : x.1 ∈ cutCore G.ambientNeckMap := G.cutCore_ambientNeckMap.symm ▸ x.property
  have hxnot : x.1 ∉ interior (cutCore G.ambientNeckMap) := by
    rwa [G.cutCore_ambientNeckMap]
  have hf : x.1 ∈ frontier (cutCore G.ambientNeckMap) := ⟨subset_closure hxcore, hxnot⟩
  rw [frontier_cutCore G.delta_pos G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding
    G.pairwise_disjoint_ambientNeckMap, ← range_cuttingSphereMap G.delta_pos G.ambientNeckMap] at hf
  obtain ⟨⟨b, y⟩, hy⟩ := hf
  apply hx
  refine mem_iUnion.mpr ⟨b, ⟨(y, ⟨0, le_rfl, cuttingCollarWidth_pos (G.delta_pos b.1)⟩), ?_⟩⟩
  apply Subtype.ext
  change G.ambientNeckMap b.1 (cuttingCollarCylinderMap (G.delta_pos b.1) b.2 _) = _
  have hz := congrArg Subtype.val (cuttingCollarMap_zero G.delta_pos G.ambientNeckMap
    G.ambientNeckMap_injective G.pairwise_disjoint_ambientNeckMap b y)
  exact hz.trans hy

theorem isCompact_coreCollarRegion_compl : IsCompact G.coreCollarRegionᶜ := by
  have hc : IsCompact (H.event i).transition.trace.tubes.core := by
    rw [← G.cutCore_ambientNeckMap]
    exact isCompact_cutCore G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding
  let : CompactSpace (H.event i).transition.trace.tubes.core := isCompact_iff_compactSpace.mp hc
  exact G.isOpen_coreCollarRegion.isClosed_compl.isCompact

theorem isCompact_component_without_coreCollars
    (x : (H.event i).transition.trace.tubes.core) :
    IsCompact (connectedComponent x \ G.coreCollarRegion) := by
  have h := G.isCompact_coreCollarRegion_compl.inter_right
    (isClosed_connectedComponent : IsClosed (connectedComponent x))
  simpa [sdiff_eq, inter_comm] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord


noncomputable section

open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

theorem ambientNeckMap_isLocalDiffeomorph (α : (H.event i).transition.trace.tubes.Index) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (G.ambientNeckMap α) := by
  apply isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_subtype_val.comp (G.neck α).chart_smooth.contMDiff)
  · intro z
    have he : mfderiv NeckCylinderModel ThreeModel (G.ambientNeckMap α) z =
        mfderiv NeckCylinderModel ThreeModel (G.neck α).chart z := by
      change mfderiv NeckCylinderModel ThreeModel
        (Subtype.val ∘ (G.neck α).chart) z = _
      rw [mfderiv_comp z ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
        ((G.neck α).chart_smooth.contMDiff.mdifferentiableAt (by simp)), mfderiv_subtype_val]
      rfl
    change Injective (mfderiv NeckCylinderModel ThreeModel (G.ambientNeckMap α) z)
    rw [he]
    exact injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel
      (G.neck α).chart z ((G.neck α).chart_smooth.isImmersion.isImmersionAt z)
  · simp [ThreeSpace]

def cutCoreDiffeomorph :
    let : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1))
        (cutCore G.ambientNeckMap) :=
      cutCoreBoundaryChartedSpace ThreeModel (by simp [ThreeSpace]) G.delta_pos
        G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding G.pairwise_disjoint_ambientNeckMap
    let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
      (H.event i).transition.coreCharts
    cutCore G.ambientNeckMap ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯
      (H.event i).transition.trace.tubes.core := by
  let : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1))
      (cutCore G.ambientNeckMap) :=
    cutCoreBoundaryChartedSpace ThreeModel (by simp [ThreeSpace]) G.delta_pos
      G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding G.pairwise_disjoint_ambientNeckMap
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.coreCharts
  let D := Homeomorph.setCongr G.cutCore_ambientNeckMap
  have hgeneric := cutCore_ambientInclusion_isSmoothEmbedding ThreeModel (by simp [ThreeSpace])
    G.delta_pos G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding
    G.pairwise_disjoint_ambientNeckMap G.ambientNeckMap_isLocalDiffeomorph
  exact {
    toEquiv := D.toEquiv
    contMDiff_toFun :=
      (ContMDiff.iff_comp_isImmersion (H.event i).transition.core_induced.isImmersion).mpr
        ⟨D.continuous, hgeneric.contMDiff⟩
    contMDiff_invFun := (ContMDiff.iff_comp_isImmersion hgeneric.isImmersion).mpr
      ⟨D.symm.continuous, (H.event i).transition.core_induced.contMDiff⟩ }

theorem coreCollar_isLocalDiffeomorph (b : (H.event i).transition.trace.tubes.Boundary) :
    let : ChartedSpace (EuclideanHalfSpace 1)
        (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (G.delta_pos b.1))
    let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
      (H.event i).transition.coreCharts
    IsLocalDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ (G.coreCollar b) := by
  let : ChartedSpace (EuclideanHalfSpace 1)
      (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (G.delta_pos b.1))
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.coreCharts
  let : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1))
      (cutCore G.ambientNeckMap) :=
    cutCoreBoundaryChartedSpace ThreeModel (by simp [ThreeSpace]) G.delta_pos
      G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding G.pairwise_disjoint_ambientNeckMap
  have hc := cuttingCollarMap_isLocalDiffeomorph ThreeModel (by simp [ThreeSpace]) G.delta_pos
    G.ambientNeckMap G.ambientNeckMap_isOpenEmbedding G.pairwise_disjoint_ambientNeckMap
    G.ambientNeckMap_isLocalDiffeomorph b
  dsimp only at hc ⊢
  intro q
  exact IsLocalDiffeomorphAt.comp (I := (𝓡 2).prod (𝓡∂ 1))
    (J := (𝓡 2).prod (𝓡∂ 1)) (K := 𝓡∂ 3) _ (hc q)
    (G.cutCoreDiffeomorph.isLocalDiffeomorph _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
