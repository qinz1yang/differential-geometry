import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelTransport

/-!
# Consumers of S3-PT.a (lane CMS3-PT, group G2)

* `exists_parallel_unit_normal_geodesicFlow`: a unit vector orthogonal to the velocity extends to a
  continuous parallel field of unit vectors orthogonal to the velocity along the whole geodesic (the
  `ξ`-part of the S3-SHIFT output shape).
* `inner_geodesicFlow_snd_eq`: geodesics of a complete finite metric have constant speed.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] {r : ℕ∞}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **Parallel unit normal along a geodesic.** -/
theorem exists_parallel_unit_normal_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) (w : E) (hw : g.inner p.proj w w = 1)
    (hwp : g.inner p.proj w p.snd = 0) :
    ∃ ξ : ℝ → E, ξ 0 = w ∧
      IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ ∧
      Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) ∧
      ∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
        g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0 := by
  obtain ⟨P, hP0, hPpar, hPc, hPiso, hPvel, -⟩ := exists_parallelTransport_geodesicFlow g hr hnorm p
  refine ⟨fun t => P t w, congrArg (fun L : E →L[ℝ] E => L w) hP0, hPpar w, hPc w, fun t => ⟨?_, ?_⟩⟩
  · rw [hPiso t w w, hw]
  · rw [← hPvel t, hPiso t w p.snd, hwp]

/-- **Geodesics have constant speed** (through parallel transport of the velocity). -/
theorem inner_geodesicFlow_snd_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) (t : ℝ) :
    g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd (g.geodesicFlow p t).snd =
      g.inner p.proj p.snd p.snd := by
  obtain ⟨P, -, -, -, hPiso, hPvel, -⟩ := exists_parallelTransport_geodesicFlow g hr hnorm p
  rw [← hPvel t, hPiso t p.snd p.snd]

end DifferentialGeometry.Geometry.FiniteSoul
