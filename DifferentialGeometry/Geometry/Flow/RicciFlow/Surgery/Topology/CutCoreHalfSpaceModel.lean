import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapTransitionSkeleton
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSmoothEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreIntrinsicBoundary

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section TubeSystemSlots

variable {M : Type u} [TopologicalSpace M]

@[instance_reducible]
def TubeSystem.coreChartedSpace (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core] :
    ChartedSpace (EuclideanHalfSpace 3) T.core :=
  euclideanHalfSpaceProdChartedSpace T.core

theorem TubeSystem.isManifold_core_of_euclideanHalfSpaceProd (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    [IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ T.core] :
    letI := T.coreChartedSpace
    IsManifold (𝓡∂ 3) ∞ T.core :=
  euclideanHalfSpaceProd_isManifold T.core

theorem TubeSystem.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    [ChartedSpace ThreeSpace M]
    (h : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (Subtype.val : T.core → M)) :
    letI := T.coreChartedSpace
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : T.core → M) :=
  DifferentialGeometry.Manifold.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd h

theorem TubeSystem.boundary_eq_iUnion_coreBoundarySphere_of_euclideanHalfSpaceProd (T : TubeSystem M)
    [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    (h : ((𝓡 2).prod (𝓡∂ 1)).boundary T.core =
      ⋃ b : T.Boundary, Set.range (T.coreBoundarySphere b)) :
    letI := T.coreChartedSpace
    (𝓡∂ 3).boundary T.core = ⋃ b : T.Boundary, Set.range (T.coreBoundarySphere b) :=
  (euclideanHalfSpaceProd_boundary T.core).trans h

theorem TubeSystem.iUnion_range_coreBoundarySphere_eq_empty (T : TubeSystem M) [IsEmpty T.Index] :
    (⋃ b : T.Boundary, Set.range (T.coreBoundarySphere b)) = ∅ := by
  apply Set.iUnion_eq_empty.mpr
  intro b
  exact isEmptyElim b.1

end TubeSystemSlots

section CappingSlot

variable {M : Type u} [TopologicalSpace M] {N : Type u} [TopologicalSpace N]

theorem Capping.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd {T : TubeSystem M}
    (K : Capping T N) [ChartedSpace EuclideanHalfSpaceProdModel T.core]
    [ChartedSpace ThreeSpace N]
    (h : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ K.coreInclusion) :
    letI := euclideanHalfSpaceProdChartedSpace T.core
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ K.coreInclusion :=
  DifferentialGeometry.Manifold.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd
    K.coreInclusion h

end CappingSlot

section CutCoreWorld

open DifferentialGeometry.Topology.ThreeManifold.Surgery

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
variable {ι : Type u} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ ThreeSpace = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

theorem cutCore_isManifold_of_euclideanHalfSpaceProd
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
  cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs

theorem cutCore_isManifold_euclideanHalfSpace
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
      cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs
    letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
    IsManifold (𝓡∂ 3) ∞ (cutCore f) :=
  letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
  letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs
  euclideanHalfSpaceProd_isManifold (cutCore f)

theorem cutCore_isSmoothEmbedding_subtypeVal_euclideanHalfSpace
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
      cutCore_isManifold ThreeModel hdim hδ f hf hdisj hs
    letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : cutCore f → M) :=
  @DifferentialGeometry.Manifold.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd M _ _
    (cutCore f)
    (cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj)
    (cutCore_ambientInclusion_isSmoothEmbedding ThreeModel hdim hδ f hf hdisj hs)

theorem cutCore_boundary_eq_iUnion_cuttingSphereAttachment_euclideanHalfSpace
    (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i)) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
    letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
    (𝓡∂ 3).boundary (cutCore f) =
      ⋃ b : ι × Bool, Set.range (fun y : Sphere 2 =>
        cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) :=
  letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel hdim hδ f hf hdisj
  letI := euclideanHalfSpaceProdChartedSpace (cutCore f)
  (euclideanHalfSpaceProd_boundary (cutCore f)).trans
    ((cutCore_boundary_eq_cuttingSpheres ThreeModel hdim hδ f hf hdisj hs).trans (by
      ext x
      constructor
      · rintro ⟨⟨b, y⟩, rfl⟩
        exact Set.mem_iUnion.mpr ⟨b, Set.mem_range_self y⟩
      · intro hx
        obtain ⟨b, y, hy⟩ := Set.mem_iUnion.mp hx
        exact ⟨⟨b, y⟩, hy⟩))

end CutCoreWorld

section StandardNeck

private def sphereTwoPoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

theorem standardNeckTubeSystem_iUnion_range_coreBoundarySphere_nonempty :
    (⋃ b : standardNeckTubeSystem.Boundary,
      Set.range (standardNeckTubeSystem.coreBoundarySphere b)).Nonempty :=
  ⟨standardNeckTubeSystem.coreBoundarySphere (PUnit.unit, false) sphereTwoPoint,
    Set.mem_iUnion.mpr ⟨(PUnit.unit, false), Set.mem_range_self sphereTwoPoint⟩⟩

end StandardNeck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
