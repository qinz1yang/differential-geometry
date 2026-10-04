import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelSlice
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelChartApplications

/-!
# Consumers of S3-PT.b (lane CMS3-PT, group G3)

`exists_parallel_mem_sliceTangent`: along a geodesic arc inside a totally geodesic slice `Z`, the
parallel transport (S3-PT.a) of a vector tangent to `Z` stays tangent to `Z` (S3-PT.b). This is the
tangency clause that the relative shave (REL kernel) asks of the transverse-shift field.
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

/-- **Parallel transport keeps tangency to a totally geodesic slice.** -/
theorem exists_parallel_mem_sliceTangent
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {k : ℕ∞} (hk : 3 ≤ k) {d : ℕ} {Z : Set M} (hZ : IsEmbeddedSliceOfOrder I (k : ℕ∞ω) d Z)
    (htg : IsTotallyGeodesicFinite g Z) (p : TangentBundle I M) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hγ : ∀ t ∈ Icc a b, (g.geodesicFlow p t).proj ∈ Z) {w : E}
    (hw : w ∈ sliceTangent I Z p.proj) :
    ∃ ξ : ℝ → E, ξ 0 = w ∧
      IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ ∧
      Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) ∧
      ∀ t ∈ Icc a b, ξ t ∈ sliceTangent I Z (g.geodesicFlow p t).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨P, hP0, hPpar, hPc, -, -, -⟩ := exists_parallelTransport_geodesicFlow g hr1 hnorm p
  have hξ0 : P 0 w = w := congrArg (fun L : E →L[ℝ] E => L w) hP0
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ_of_one_le g hr1 hnorm
  have hdom : ∀ t : ℝ, (p, t) ∈ g.geodesicFlowDomain := fun t => by rw [hD]; exact mem_univ _
  have hIcc : IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) (fun t => P t w)
      (Icc a b) := by
    rcases lt_or_ge a b with hab | hab
    · refine (isParallelAlongFinite_geodesicFlow_iff hr1 (fun t _ => hdom t)
        (fun t ht => uniqueDiffOn_Icc hab t ht)).2 fun t _ q hq => ?_
      exact ((isParallelAlongFinite_geodesicFlow_iff hr1 (fun t _ => hdom t)
        (fun t _ => uniqueDiffWithinAt_univ)).1 (hPpar w) t (mem_univ t) q hq).mono
          (subset_univ _)
    · have hab' : a = b := le_antisymm (ha.trans hb) hab
      rw [hab']
      exact isParallelAlongFinite_Icc_self g _ _ b
  refine ⟨fun t => P t w, hξ0, hPpar w, hPc w, ?_⟩
  exact isParallel_mem_sliceTangent_of_totallyGeodesic g hr hnorm hk hZ htg p ha hb hγ
    (fun t => P t w) (hPc w).continuousOn hIcc (by rw [hξ0]; exact hw)

end DifferentialGeometry.Geometry.FiniteSoul
