import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Geometry.Metric.UniformCharts








open Set Bundle Manifold DifferentialGeometry
open scoped ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

private theorem closedCube_subset_closedBall :
    plateauClosedCube ⊆ Metric.closedBall (0 : plateauCoordinateSpace) 2 := by
  intro y hy
  rw [EuclideanSpace.closedBall_zero_eq 2 (by norm_num)]
  change ∑ i : Fin 3, y i ^ 2 ≤ (2 : ℝ) ^ 2
  have hs : ∑ i : Fin 3, y i ^ 2 ≤ ∑ _ : Fin 3, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have hi := abs_le.mp (hy i)
    nlinarith
  norm_num at hs ⊢
  linarith




theorem homogeneouslyRegularMetric_of_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) : HomogeneouslyRegularMetric g := by
  classical
  by_cases hM : Nonempty M
  · let := hM
    let e : plateauCoordinateSpace ≃L[ℝ] E :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [hd, plateauCoordinateSpace])
    obtain ⟨m, A, hm, hmA, ψ, hψ, hC⟩ := exists_uniform_metric_charts g e 2
      (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ))
    have hball : plateauOpenCube ⊆ Metric.closedBall (0 : plateauCoordinateSpace) 2 :=
      fun y hy => closedCube_subset_closedBall (fun i => (hy i).le)
    refine ⟨m, A, hm, hmA, ψ, ?_, ?_⟩
    · intro p
      exact ⟨closedCube_subset_closedBall.trans (hψ p).1, (hψ p).2.1,
        (hψ p).2.2.1, (hψ p).2.2.2.1, fun y hy => (hψ p).2.2.2.2 y (hball hy)⟩
    · intro k
      obtain ⟨C, hC0, hC⟩ := hC k
      exact ⟨C, hC0, fun p i j y hy => hC p i j y (hball hy)⟩
  · let : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨1, 1, zero_lt_one, le_rfl, (fun p => isEmptyElim p), ?_, ?_⟩
    · exact fun p => isEmptyElim p
    · exact fun _ => ⟨0, le_rfl, fun p => isEmptyElim p⟩

end DifferentialGeometry.Geometry
