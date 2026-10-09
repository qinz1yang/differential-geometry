import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothDirections
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness

/-!
# Hopf–Rinow for a complete smooth metric, in the ported (finite-order) language

The frozen CM2.b statement `hopfRinow_finite` for a SMOOTH metric, obtained by calling the
existing smooth development through the row-3 bridge instead of re-proving it: minimizing unit
directions from the soul toolkit (`soul_unit_minimizing_initial`, smooth `minExp`), translated by
`expMap_smul_eq_intrinsicGeodesic`, plus the finite-order speed bound and completeness of the flow
(`Completeness.lean`). Lane CM-H, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Hopf–Rinow for a complete smooth metric** (the frozen CM2.b statement at `n = ∞`), through the
smooth API: proper, flow complete, and every two points joined by a minimizing radial geodesic of
the ported exponential map. -/
theorem hopfRinow_smooth (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g) :
    ProperSpace M ∧ g.geodesicFlowDomain = univ ∧
      ∀ x y : M, ∃ u : E, g.inner x u u = 1 ∧
        ∀ t ∈ Icc 0 (dist x y), dist x (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = t ∧
          g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y := by
  refine ⟨Manifold.properSpace_of_isRiemannianManifold I,
    geodesicFlowDomain_eq_univ_of_isMetricNorm g hEnorm, fun x y => ?_⟩
  have hexp0 : ∀ u : E, g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := fun u => by
    rw [zero_smul]
    exact g.expMap_zero (r := ⊤) le_top x
  rcases eq_or_lt_of_le (dist_nonneg (x := x) (y := y)) with hd | hd
  · obtain ⟨u, hu⟩ := g.exists_inner_self_eq_one (r := ⊤) x
    have hxy : x = y := dist_eq_zero.mp hd.symm
    refine ⟨u, hu, fun t ht => ?_⟩
    rw [← hd] at ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [ht0, ← hd, hexp0, dist_self]
    exact ⟨rfl, hxy⟩
  obtain ⟨u, hu, hend⟩ :=
    DifferentialGeometry.Geometry.Topology.soul_unit_minimizing_initial g hEnorm x y hd
  have hy : g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y :=
    (expMap_smul_eq_intrinsicGeodesic g hEnorm x u (dist x y)).trans hend
  have hlip : ∀ s t : ℝ, dist (g.expMap (⟨x, s • u⟩ : TangentBundle I M))
      (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) ≤ Real.sqrt (g.inner x u u) * |t - s| :=
    fun s t => g.dist_expMap_smul_le_of_completeSpace (r := ⊤) le_top hEnorm u s t
  have hx0 : g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := hexp0 u
  refine ⟨u, hu, fun t ht => ⟨?_, hy⟩⟩
  change dist x (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = t
  have h1 := hlip 0 t
  rw [hx0, hu, Real.sqrt_one, one_mul, sub_zero, abs_of_nonneg ht.1] at h1
  have h2 := hlip t (dist x y)
  rw [hy, hu, Real.sqrt_one, one_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)] at h2
  have htri := dist_triangle x (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) y
  linarith

end Bundle.ContMDiffRiemannianMetric
