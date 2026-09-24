import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection

noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {M : Type*} [TopologicalSpace M] {ι κ : Type*} {δ : ι → ℝ}
  (f : ∀ i, bufferedCylinder (δ i) → M) (e : κ ≃ ι)

omit [TopologicalSpace M] in
theorem cutCore_reindex : cutCore (fun j => f (e j)) = cutCore f := by
  unfold cutCore
  congr 1
  exact iUnion_congr_of_surjective e e.surjective (fun _ => rfl)

omit [TopologicalSpace M] in
theorem pairwise_disjoint_reindex
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j))) :
    Pairwise fun i j => Disjoint (range (f (e i))) (range (f (e j))) :=
  fun _ _ hij => hdisj (fun h => hij (e.injective h))

variable (hδ : ∀ i, 0 < δ i) (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))

theorem cuttingSphereComponent_map_reindex (b : κ × Bool) :
    (Homeomorph.setCongr (cutCore_reindex f e)).continuous.connectedComponentsMap
      (cuttingSphereComponent (fun j => hδ (e j)) (fun j => f (e j)) (fun j => hf (e j))
        (pairwise_disjoint_reindex f e hdisj) b) =
      cuttingSphereComponent hδ f hf hdisj (e b.1, b.2) := rfl

end DifferentialGeometry.Topology.ThreeManifold.Surgery
