import DifferentialGeometry.Geometry.Metric.TangentTube



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]



theorem exists_uniform_fiber_injectivity (g : SmoothRiemannianMetric I M)
    {Y : Type*} (F : TangentBundle I M → Y)
    (hbase : ∀ u v, F u = F v → u.proj = v.proj)
    (hloc : ∀ x : M, ∃ U : Set (TangentBundle I M),
      IsOpen U ∧ (TotalSpace.mk' E x 0 : TangentBundle I M) ∈ U ∧ InjOn F U) :
    ∃ ε : ℝ, 0 < ε ∧ InjOn F
      {u : TangentBundle I M | Real.sqrt (g.inner u.proj u.2 u.2) ≤ ε} := by
  classical
  choose U hU hzero hF using hloc
  let W : Set (TangentBundle I M × TangentBundle I M) := ⋃ x : M, U x ×ˢ U x
  have hW : IsOpen W := isOpen_iUnion (fun x => (hU x).prod (hU x))
  have hz (x : M) :
      ((TotalSpace.mk' E x 0 : TangentBundle I M), TotalSpace.mk' E x 0) ∈ W :=
    mem_iUnion.mpr ⟨x, hzero x, hzero x⟩
  obtain ⟨ε, hε, hpairs⟩ := exists_metric_tangent_pair_radius g hW hz
  refine ⟨ε, hε, fun u hu v hv huv => ?_⟩
  obtain ⟨x, hux, hvx⟩ := mem_iUnion.mp (hpairs u v (hbase u v huv) hu hv)
  exact hF x hux hvx huv

end DifferentialGeometry.Geometry
