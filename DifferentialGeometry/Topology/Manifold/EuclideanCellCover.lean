import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Tactic
import DifferentialGeometry.Topology.Cellular.Cellular

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology

theorem exists_openEmbedding_euclidean_at {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → M, IsOpenEmbedding φ ∧ φ 0 = x := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) (mem_chart_target _ x)
  let u : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    OpenPartialHomeomorph.univBall (c x) r
  have hu_source : u.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hu_target : u.target = ball (c x) r := OpenPartialHomeomorph.univBall_target _ hr
  let ψ := u.trans c.symm
  have hsource : ψ.source = univ := by
    ext v
    simp only [ψ, OpenPartialHomeomorph.trans_source, mem_inter_iff, hu_source,
      mem_univ, true_and, mem_preimage, iff_true]
    exact hball (hu_target ▸ u.map_source (hu_source ▸ mem_univ v))
  refine ⟨ψ, ψ.isOpenEmbedding hsource, ?_⟩
  change c.symm (OpenPartialHomeomorph.univBall (c x) r 0) = x
  rw [OpenPartialHomeomorph.univBall_apply_zero]
  exact c.left_inv (mem_chart_source _ x)

theorem exists_finite_euclidean_cell_cover {n : ℕ} {M : Type*}
    [TopologicalSpace M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∃ k : ℕ, ∃ φ : Fin k → EuclideanSpace ℝ (Fin n) → M,
      (∀ i, IsOpenEmbedding (φ i)) ∧
      (⋃ i, φ i '' ball 0 (1 / 2 : ℝ)) = univ ∧
      (∀ i, IsCompact (φ i '' closedBall 0 1)) := by
  classical
  choose φ hφ hcenter using
    (fun x : M => exists_openEmbedding_euclidean_at (n := n) x)
  have hcover : (univ : Set M) ⊆ ⋃ x, φ x '' ball 0 (1 / 2 : ℝ) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, 0, by simp, hcenter x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => φ x '' ball 0 (1 / 2 : ℝ))
    (fun x => (hφ x).isOpenMap _ isOpen_ball) hcover
  let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (by simp)).symm
  refine ⟨s.card, fun i => φ (e i), fun i => hφ (e i), ?_, ?_⟩
  · apply eq_univ_of_univ_subset
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hxy
  · intro i
    exact (isCompact_closedBall _ _).image (hφ (e i)).continuous

def EmbeddedClosedCell.ofOpenEmbedding {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (φ : EuclideanSpace ℝ (Fin n) → M) (hφ : IsOpenEmbedding φ) : EmbeddedClosedCell n M where
  map := φ ∘ Subtype.val
  isClosedEmbedding := by
    have : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    exact (hφ.continuous.comp continuous_subtype_val).isClosedEmbedding
      (hφ.injective.comp Subtype.val_injective)
  isOpen_interior := by
    change IsOpen ((φ ∘ Subtype.val) '' (Subtype.val ⁻¹' ball 0 1))
    rw [image_comp, image_preimage_eq_of_subset]
    · exact hφ.isOpenMap _ isOpen_ball
    · simpa only [Subtype.range_coe] using
        (ball_subset_closedBall : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ closedBall 0 1)

@[simp]
theorem EmbeddedClosedCell.ofOpenEmbedding_interiorSet {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M]
    (φ : EuclideanSpace ℝ (Fin n) → M) (hφ : IsOpenEmbedding φ) :
    (EmbeddedClosedCell.ofOpenEmbedding φ hφ).interiorSet = φ '' ball 0 1 := by
  change (φ ∘ Subtype.val) '' (Subtype.val ⁻¹' ball 0 1) = _
  rw [image_comp, image_preimage_eq_of_subset]
  simpa only [Subtype.range_coe] using
    (ball_subset_closedBall : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ closedBall 0 1)

theorem exists_finite_embeddedClosedCell_cover {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∃ k : ℕ, ∃ c : Fin k → EmbeddedClosedCell n M, (⋃ i, (c i).interiorSet) = univ := by
  obtain ⟨k, φ, hφ, hcover, -⟩ := exists_finite_euclidean_cell_cover (n := n) (M := M)
  refine ⟨k, fun i => .ofOpenEmbedding (φ i) (hφ i), eq_univ_of_univ_subset ?_⟩
  rw [← hcover]
  apply iUnion_mono
  intro i
  rw [EmbeddedClosedCell.ofOpenEmbedding_interiorSet]
  exact image_mono (ball_subset_ball (by norm_num))

end DifferentialGeometry.Topology
