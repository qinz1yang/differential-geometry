import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhood

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Collar (δ : ℝ) := S2 × Ico (0 : ℝ) (cuttingCollarWidth δ)
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ}

theorem cuttingCollar_frontier_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (q : Collar (precision b.1)) :
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).val ∈ frontier (cutCore f) ↔
      q.2.val = 0 := by
  constructor
  · intro hq
    have hr : cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q ∈
        range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact hq
    obtain ⟨a, ha⟩ := hr
    have hb := (cuttingSphereAttachment_mem_collar_iff hδ f (fun i => (hf i).injective) hdisj a b).mp
      ⟨q, ha.symm⟩
    rcases a with ⟨c, y⟩
    change c = b at hb
    subst c
    have hz := (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans ha
    have he := (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b).injective hz
    exact (congrArg (fun p : Collar (precision b.1) => p.2.val) he).symm
  · intro hq
    have he : q = (q.1, ⟨0, ⟨le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩⟩) :=
      Prod.ext rfl (Subtype.ext hq)
    rw [he, cuttingCollarMap_zero]
    have hr : cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, q.1⟩ ∈
        range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := ⟨⟨b, q.1⟩, rfl⟩
    rw [range_cuttingSphereAttachment hδ f hf hdisj] at hr
    exact hr

theorem cuttingCollar_interior_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (q : Collar (precision b.1)) :
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).val ∈ interior (cutCore f) ↔
      0 < q.2.val := by
  have hc := (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).property
  constructor
  · intro hi
    have hn : q.2.val ≠ 0 := by
      intro hz
      have hfront := (cuttingCollar_frontier_iff hδ f hf hdisj b q).mpr hz
      exact hfront.2 hi
    exact lt_of_le_of_ne q.2.property.1 hn.symm
  · intro ht
    by_contra hi
    have hfront : (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).val ∈
        frontier (cutCore f) := ⟨subset_closure hc, hi⟩
    exact (ne_of_gt ht) ((cuttingCollar_frontier_iff hδ f hf hdisj b q).mp hfront)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
