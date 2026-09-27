import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import DifferentialGeometry.Topology.SphereSeparation.BallSideRelations
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem exists_ball_chart_inside_ball_of_sphere_embedding
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : closedBall (0 : E3) 1 ⊆ C.source)
    (e : S2 → M) (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hinside : range e ⊆ C '' ball (0 : E3) 1) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' sphere (0 : E3) 1 = range e ∧
      B '' closedBall (0 : E3) 1 ⊆ C '' ball (0 : E3) 1 := by
  have hes : range e ⊆ C.target := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hinside hx
    exact C.map_source (hC (ball_subset_closedBall hy))
  let f : S2 → E3 := C.symm ∘ e
  have hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph C.symm he hes
  have hfball : range f ⊆ ball (0 : E3) 1 := by
    rintro x ⟨q, rfl⟩
    obtain ⟨z, hz, heq⟩ := hinside (mem_range_self q)
    change C.symm (e q) ∈ _
    rw [← heq]
    have hinv : C.toPartialEquiv.symm (C.toPartialEquiv z) = z :=
      C.toPartialEquiv.left_inv (hC (ball_subset_closedBall hz))
    change C.toPartialEquiv.symm (C.toPartialEquiv z) ∈ ball (0 : E3) 1
    rw [hinv]
    exact hz
  have hfconn : IsConnected (range f) := by
    have hs : IsConnected (univ : Set S2) := by
      let _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
        (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E3]))
          (0 : E3) zero_le_one)
      exact isConnected_univ
    simpa only [image_univ] using hs.image f hf.contMDiff.continuous.continuousOn
  let d := SphereSeparation.jordanBrouwer_openThreeSpace f hf (Diffeomorph.refl (𝓡 3) E3 ∞)
  have hdsub : closure d.compactSide ⊆ ball (0 : E3) 1 := by
    apply SphereSeparation.standardUnitSphereSides.closure_compactSide_subset_of_sphere_subset
      d.toSphereSides ?_ hfconn hfball
    rw [disjoint_left]
    intro x hxS hxf
    have hball := hfball hxf
    exact (mem_ball.mp hball).ne (mem_sphere.mp hxS)
  have hSch : SphereSeparation.smoothSchoenfliesThree :=
    SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr
      smooth_schoenflies_three
  obtain ⟨D, hD⟩ :=
    SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp hSch f hf
  have hDclosed : D '' closedBall (0 : E3) 1 = closure d.compactSide := by
    calc
      _ = D '' closure (ball (0 : E3) 1) := by rw [closure_ball _ one_ne_zero]
      _ = closure (D '' ball (0 : E3) 1) := D.toHomeomorph.image_closure _
      _ = _ := by rw [hD]
  have hDsphere : D '' sphere (0 : E3) 1 = range f := by
    calc
      _ = D '' frontier (ball (0 : E3) 1) := by rw [frontier_ball _ one_ne_zero]
      _ = frontier (D '' ball (0 : E3) 1) := D.toHomeomorph.image_frontier _
      _ = _ := by rw [hD]; exact d.frontier_compactSide
  let B := D.toPartialDiffeomorph.trans C
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hC (ball_subset_closedBall (hdsub (hDclosed ▸ mem_image_of_mem D hx)))⟩
  · change (C ∘ D) '' sphere (0 : E3) 1 = range e
    rw [image_comp, hDsphere, ← range_comp]
    apply congrArg range
    funext q
    exact C.right_inv (hes (mem_range_self q))
  · change (C ∘ D) '' closedBall (0 : E3) 1 ⊆ C '' ball (0 : E3) 1
    rw [image_comp, hDclosed]
    exact image_mono hdsub

end DifferentialGeometry.Topology.ThreeManifold
