import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacketSlice
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.ClosedBall

/-!
# The original LFR28 disk of an edge disk packet as a smooth embedding into the ambient 3-manifold

Lane S-EDP-FDC, group G3 (EDP04 whole-disk binding, step A). Draft 74 D74-11: "`fibre_disk` by
EDP04's whole-trace isotopy to the ORIGINAL disk (output: smooth embedding)". The packet's
`diskModel` (LC84) is a diffeomorphism of `ClosedCell 2` onto the regular sublevel
`{η_p = 0, H ≤ 4Δ}` of the slab (a manifold with boundary, slab re-charted on `ℝ × ℝ²`). The disk
extends across the rim into the boundaryless regular slice `{η_p = 0}` (`exists_sliceChart`), and
the slice is a smooth surface embedded in the slab and in `M`:

* `EdgeDiskPacket.exists_slice_embedding_EFE`: a smooth embedding `ClosedCell 2 → Slice` equal to
  `diskModel` as a map into `M` (a local diffeomorphism composed with the closed-cell inclusion);
* `EdgeDiskPacket.isSmoothEmbedding_sliceVal_EFE`: the slice inclusion `Slice → M` is a smooth
  embedding for the standard `𝓘(ℝ, E3)` structure of `M` (the slab is re-charted along the linear
  identification `E3 ≃L ℝ × E2`, whose effect on embeddings is `…_source_iff`);
* **`EdgeDiskPacket.exists_smoothDisk_EFE`**: a smooth embedding `φ : ClosedCell 2 → M` onto the
  WHOLE fibre `{y ∈ B(center, 100Δ) : η_p y = 0, H y ≤ 4Δ}` with the boundary circle onto the rim
  `{H = 4Δ}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

section Packet

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
  {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}

theorem EdgeDiskPacket.exists_slice_embedding_EFE
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
      P.contMDiff_height_slab P.regular_fibre P.regular_boundary
    letI := P.sliceChartedSpace
    ∃ φ : ClosedCell 2 → P.Slice, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ φ ∧
      ∀ z : ClosedCell 2, (((φ z).1 : P.slabOpen) : M) = ((P.diskModel z).1 : M) := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let _ := P.sliceChartedSpace
  have _ : IsManifold (𝓡 2) ∞ P.Slice := P.slice_isManifold
  obtain ⟨j, hjs, hjD⟩ := P.exists_sliceChart
  have hinc : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞
      (Subtype.val : ClosedCell 2 → E2) := Handle.closedCellInclusion_isSmoothEmbedding 1
  have hmem : ∀ z : ClosedCell 2, (z : E2) ∈ j.source := fun z =>
    hjs (by rw [mem_closedBall_zero_iff]; exact z.2)
  have hloc : IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ j (range (Subtype.val : ClosedCell 2 → E2)) := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hy
    exact ⟨j, hmem z, fun _ _ => rfl⟩
  have himm := hinc.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero hloc (by simp)
  have hcont : Continuous (fun z : ClosedCell 2 => j (z : E2)) :=
    j.contMDiffOn.continuousOn.comp_continuous continuous_subtype_val hmem
  have hinj : Injective (fun z : ClosedCell 2 => j (z : E2)) := by
    intro z z' h
    exact Subtype.ext (j.toOpenPartialHomeomorph.injOn (hmem z) (hmem z') h)
  refine ⟨fun z => j (z : E2), ⟨himm, ?_⟩, fun z => hjD z⟩
  exact (hcont.isClosedEmbedding hinj).isEmbedding

theorem EdgeDiskPacket.isSmoothEmbedding_sliceVal_EFE
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI := P.sliceChartedSpace
    IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ (fun s : P.Slice => ((s.1 : P.slabOpen) : M)) := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := P.sliceChartedSpace
  have _ : IsManifold (𝓡 2) ∞ P.Slice := P.slice_isManifold
  have hfib : IsSmoothEmbedding (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (Subtype.val : P.Slice → P.slabRegular) := by
    refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp)
      (DifferentialGeometry.Topology.Manifold.contMDiff_submersionFiberInclusion
        (fun y : P.slabRegular => P.coord ((y : P.slabOpen) : M)) 0
        P.isSubmersionAt_coord_slabRegular)
      (DifferentialGeometry.Topology.Manifold.mfderiv_submersionFiberInclusion_injective
        (fun y : P.slabRegular => P.coord ((y : P.slabOpen) : M)) 0
        P.isSubmersionAt_coord_slabRegular), Topology.IsEmbedding.subtypeVal⟩
  have h1 : IsSmoothEmbedding (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun s : P.Slice => ((s.1 : P.slabRegular) : P.slabOpen)) :=
    IsSmoothEmbedding.comp (IsSmoothEmbedding.of_opens P.slabRegular) hfib (by simp)
  have h2 : IsSmoothEmbedding (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) ∞
      (Subtype.val : P.slabOpen → M) :=
    (DifferentialGeometry.Manifold.isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff
      𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) euclideanThreeProdHomeomorph euclideanThreeProdEquiv
      euclideanThreeProd_compat 𝓘(ℝ, E3) (N := P.slabOpen) (f := Subtype.val)).mpr
      (IsSmoothEmbedding.of_opens P.slabOpen)
  exact IsSmoothEmbedding.comp h2 h1 (by simp)

/-- **The original LFR28 disk as a smooth embedding into the ambient 3-manifold.** -/
theorem EdgeDiskPacket.exists_smoothDisk_EFE
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) (hΔ : 0 < Δ) :
    ∃ φ : ClosedCell 2 → M, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {y | y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {y | y ∈ ball P.center (100 * Δ) ∧
        P.coord y = 0 ∧ edgeRowHeight Δ F ρ y = 4 * Δ} := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let _ := P.sliceChartedSpace
  have _ : IsManifold (𝓡 2) ∞ P.Slice := P.slice_isManifold
  obtain ⟨φs, hφs, hval⟩ := P.exists_slice_embedding_EFE
  have hemb := P.isSmoothEmbedding_sliceVal_EFE
  have hcomp := Manifold.IsSmoothEmbedding.comp_of_smoothBoundary hemb hφs
  have hslab : ∀ w : P.slabOpen, ((w : P.slabOpen) : M) ∈ ball P.center (100 * Δ) := fun w =>
    ball_subset_ball (by linarith) (P.slabOpen_subset w.2)
  have hmemO : ∀ y : M, y ∈ ball P.center (100 * Δ) → P.coord y = 0 →
      edgeRowHeight Δ F ρ y ≤ 4 * Δ → y ∈ P.slabOpen := fun y hy hc hH =>
    P.slab_subset y hy (by rw [hc, abs_zero]; positivity) hH
  have hbd : ∀ z : ClosedCell 2, (𝓡∂ 2).IsBoundaryPoint z ↔ ‖(z : E2)‖ = 1 := fun z =>
    Set.ext_iff.mp (DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1) z
  have hDb : ∀ z : ClosedCell 2, (𝓡∂ 2).IsBoundaryPoint (P.diskModel z) ↔
      (𝓡∂ 2).IsBoundaryPoint z := fun z =>
    ((P.diskModel.isLocalDiffeomorph z).isBoundaryPoint_iff (by simp)).symm
  refine ⟨(fun s : P.Slice => ((s.1 : P.slabOpen) : M)) ∘ φs, hcomp, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      rw [Function.comp_apply, hval z]
      obtain ⟨hc, hH⟩ := (P.diskModel z).2
      exact ⟨hslab _, hc, by linarith⟩
    · rintro ⟨hy, hc, hH⟩
      let w : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} :=
        ⟨⟨y, hmemO y hy hc hH⟩, hc, by linarith⟩
      refine ⟨P.diskModel.symm w, ?_⟩
      rw [Function.comp_apply, hval, Diffeomorph.apply_symm_apply]
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Function.comp_apply, Function.comp_apply, hval]
      have hzb : (𝓡∂ 2).IsBoundaryPoint (cellBoundaryInclusion 2 x) := (hbd _).mpr x.2
      have hHH := P.boundary_level.1 (P.diskModel (cellBoundaryInclusion 2 x)) ((hDb _).mpr hzb)
      exact ⟨hslab _, (P.diskModel (cellBoundaryInclusion 2 x)).2.1, hHH⟩
    · rintro ⟨hy, hc, hH⟩
      let w : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} :=
        ⟨⟨y, hmemO y hy hc hH.le⟩, hc, by linarith⟩
      have hwb : (𝓡∂ 2).IsBoundaryPoint w := P.boundary_level.2 w hH
      have hzb : (𝓡∂ 2).IsBoundaryPoint (P.diskModel.symm w) := by
        refine (hDb _).mp ?_
        rw [Diffeomorph.apply_symm_apply]
        exact hwb
      refine ⟨⟨((P.diskModel.symm w : ClosedCell 2) : E2), (hbd _).mp hzb⟩, ?_⟩
      rw [Function.comp_apply, Function.comp_apply, hval]
      change (((P.diskModel (P.diskModel.symm w)).1 : P.slabOpen) : M) = y
      rw [Diffeomorph.apply_symm_apply]

end Packet

end DifferentialGeometry.Geometry.Collapse
