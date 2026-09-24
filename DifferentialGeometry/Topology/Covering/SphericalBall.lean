import DifferentialGeometry.Topology.Covering.SphereLifts
import DifferentialGeometry.Topology.SphereSeparation.InnermostBall
import DifferentialGeometry.Topology.Covering.RegionDescent
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Embedding.Frontier

section

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]

omit [IsManifold (𝓡 3) ∞ M] in
theorem exists_ball_chart_of_spherical_cover
    {p : S3 → M} (hp : IsCoveringMap p) (honto : Function.Surjective p)
    (hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (e : SphereTwo → M) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {x : M} (hx : x ∉ range e) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      Metric.closedBall (0 : E3) 1 ⊆ G.source ∧
      G '' Metric.sphere (0 : E3) 1 = range e := by
  let z₀ : SphereTwo := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨north, hnorth⟩ := honto x
  obtain ⟨lifts, hbase, hemb, hproj, hdis, hcover⟩ :=
    exists_disjoint_smooth_sphere_lifts hp hlocal e he z₀
  let _ : Finite (p ⁻¹' {e z₀}) :=
    Geometry.Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact hp _
  let _ : Nonempty (p ⁻¹' {e z₀}) := by
    obtain ⟨y, hy⟩ := honto (e z₀)
    exact ⟨y, hy⟩
  have hmiss (a : p ⁻¹' {e z₀}) : north ∉ range (lifts a) := by
    rintro ⟨z, hz⟩
    apply hx
    exact ⟨z, (hproj a z).symm.trans ((congrArg p hz).trans hnorth)⟩
  obtain ⟨a, F, hFsrc, hFsphere, hFavoid⟩ :=
    SphereSeparation.exists_innermost_ball_of_sphere_family lifts hemb hdis north hmiss
  have hFcont : Continuous (F : E3 → S3) :=
    (contMDiffOn_univ.mp (hFsrc ▸ F.contMDiffOn_toFun)).continuous
  have hFemb : _root_.Topology.IsOpenEmbedding (F : E3 → S3) :=
    F.toOpenPartialHomeomorph.isOpenEmbedding hFsrc
  let B := F '' Metric.ball (0 : E3) 1
  have hBopen : IsOpen B := hFemb.isOpenMap _ Metric.isOpen_ball
  have hBconn : IsConnected B := (convex_ball (0 : E3) (1 : ℝ)).isConnected
    ⟨0, Metric.mem_ball_self zero_lt_one⟩ |>.image F hFcont.continuousOn
  have hKcompact : IsCompact (F '' Metric.closedBall (0 : E3) 1) :=
    (isCompact_closedBall (0 : E3) 1).image hFcont
  have hBclosure : closure B = F '' Metric.closedBall (0 : E3) 1 := by
    apply subset_antisymm
    · exact closure_minimal (image_mono Metric.ball_subset_closedBall) hKcompact.isClosed
    · rw [← closure_ball (0 : E3) one_ne_zero]
      exact image_closure_subset_closure_image hFcont
  have hBfront : frontier B = range (lifts a) := by
    rw [← hFsphere, frontier, hBclosure, hBopen.interior_eq]
    change F '' Metric.closedBall (0 : E3) 1 \ F '' Metric.ball (0 : E3) 1 = F '' Metric.sphere (0 : E3) 1
    rw [← image_sdiff hFemb.injective]
    congr 1
    ext z
    simp only [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere, mem_sdiff, not_lt]
    exact le_antisymm_iff.symm
  have hBavoid : Disjoint B (p ⁻¹' range e) := by rw [hcover]; exact hFavoid
  let _ : SimplyConnectedSpace S3 := inferInstance
  let _ : LocallyPathConnectedSpace S3 := ChartedSpace.locallyPathConnectedSpace E3 S3
  have hinj := DifferentialGeometry.IsCoveringMap.injOn_closure_of_lifted_frontier hp he.isEmbedding.injective (hproj a)
    hBopen hBconn.isPreconnected hBfront hBavoid
  have hcompinj : InjOn (p ∘ F) (Metric.closedBall (0 : E3) 1) := by
    intro z hz w hw hzw
    apply hFemb.injective
    apply hinj
    · rw [hBclosure]; exact mem_image_of_mem _ hz
    · rw [hBclosure]; exact mem_image_of_mem _ hw
    · exact hzw
  have hcompLocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (p ∘ F) (Metric.closedBall (0 : E3) 1) := by
    intro z
    have hf := F.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (x := z.val)
      (by rw [hFsrc]; trivial)
    exact hf.comp (𝓡 3) M (hlocal (F z.val))
  obtain ⟨G, hGsrc, hG⟩ := DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact hcompLocal
    (isCompact_closedBall (0 : E3) 1) ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hcompinj
  refine ⟨G, hGsrc, ?_⟩
  rw [hG, image_comp, hFsphere, ← range_comp]
  exact congrArg range (funext (hproj a))

end DifferentialGeometry.Topology

end

end
