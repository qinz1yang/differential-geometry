import DifferentialGeometry.Geometry.Comparison.FiniteSoul.Separation
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RayExhaustionConvex

/-!
# Consumer of the separation lemma: strict outward vectors for the convex exhaustion

`exists_unit_strict_outward_rayExhaustion`: in a complete finite metric with `sec ≥ 0`, if every
direction of a compact nonempty set `K` of `g_q`-unit vectors starts an arc along which the convex
exhaustion `f = rayExhaustion o` drops strictly below `f q`, then one `g_q`-unit vector has negative
pairing with all of `K`. This is the case `q ∉ C₀` of LFR45.1 (external review §3: `C = M`, `φ = f`),
combining S-BUS (convexity of `f` along every geodesic, `f` is `1`-Lipschitz) with S-SEP.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (rayExhaustion lipschitzWith_rayExhaustion)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- Strict outward unit vectors for the convex exhaustion (LFR45.1, case `q ∉ C₀`). -/
theorem exists_unit_strict_outward_rayExhaustion
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o q : M) {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hK : ∀ u ∈ K, g.inner q u u = 1 ∧ ∃ δ > (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) δ,
      rayExhaustion o (g.expMap (⟨q, t • u⟩ : TangentBundle I M)) < rayExhaustion o q) :
    ∃ v : E, g.inner q v v = 1 ∧ ∀ u ∈ K, g.inner q v u < 0 := by
  refine exists_unit_strict_outward_of_descent g hr hnorm (isTotallyConvexFinite_univ g)
    (lipschitzWith_rayExhaustion o)
    (fun p ℓ _ _ => (convexOn_rayExhaustion_geodesicFlow g hr hnorm hsec o p).subset
      (subset_univ _) (convex_Icc 0 ℓ)) hKc hKne fun u hu => ⟨(hK u hu).1, ?_⟩
  obtain ⟨δ, hδ, hdrop⟩ := (hK u hu).2
  exact ⟨δ, hδ, fun _ _ => mem_univ _, hdrop⟩

end DifferentialGeometry.Geometry.FiniteSoul
