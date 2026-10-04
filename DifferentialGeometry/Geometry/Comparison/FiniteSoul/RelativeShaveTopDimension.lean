import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveGeneralApplications
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftGeneralApplications

/-!
# Theorem A: the general-dimension top shave (lane CMS3-REL, group G1)

Frozen interface A of `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`
(`concaveOn_infDist_frontier_geodesicFlow_of_parallel`): for a complete metric `g` of class
`C^{r+1}` (`3 ≤ r`, `hnorm`) with `sec ≥ 0` in ANY dimension and a closed totally convex set `C`,
`t ↦ d(γ_p t, ∂C)` is concave on every interval `[0, ℓ]` mapped into `C`.

Proof: CMS3-SHAVE's A1 + A2 with the transverse shift inline
(`concaveOn_infDist_frontier_of_transverseShift`, `ShaveGeneralApplications.lean`), fed with CMS3-SHIFT's
general-dimension supplier (`transverseShift_hypothesis_of_sectional_nonneg`, which drops the parallel
and continuity conjuncts of `exists_transverse_shift_lipschitz` and restricts `∀ t` to `Icc 0 L`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **A. General-dimension S-SHAVE** (`3 ≤ r`, `sec ≥ 0`, any dimension): A1 + A2 + S3-SHIFT. The
frozen D-CMS3 statement, verbatim. -/
theorem concaveOn_infDist_frontier_geodesicFlow_of_parallel [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M)
    (ℓ : ℝ) (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ) (fun t => infDist (g.geodesicFlow p t).proj (frontier C)) :=
  concaveOn_infDist_frontier_of_transverseShift g (le_trans (by norm_num) hr) hnorm hsec
    (transverseShift_hypothesis_of_sectional_nonneg g hr hnorm hsec) hCcl hconv p ℓ hmaps

end DifferentialGeometry.Geometry.FiniteSoul

end
