import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveConcavity

/-!
# Consumers of the REL kernel and binding (CMS3-REL, G2)

* `min_le_infDist_relBoundaryOfOrder_geodesicFlow`: minimum principle for `d(·, B)` along arcs of `C`.
* `isTotallyConvexFinite_superlevel_infDist_relBoundaryOfOrder`: superlevel sets of `d(·, B)` in `C`
  are totally convex (the relative B5.1; input of DROP).
* `relBoundaryOfOrder_eq_frontier`: in full relative dimension `B = ∂C` for closed `C`, so the REL
  binding contains theorem A there (example).
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

/-- **Minimum principle** for the relative boundary distance along a geodesic arc of `C`. -/
theorem min_le_infDist_relBoundaryOfOrder_geodesicFlow [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) {t : ℝ}
    (ht : t ∈ Icc 0 ℓ) :
    min (infDist (g.geodesicFlow p 0).proj (relBoundaryOfOrder I (r : ℕ∞ω) C))
        (infDist (g.geodesicFlow p ℓ).proj (relBoundaryOfOrder I (r : ℕ∞ω) C)) ≤
      infDist (g.geodesicFlow p t).proj (relBoundaryOfOrder I (r : ℕ∞ω) C) :=
  (concaveOn_infDist_relBoundaryOfOrder_geodesicFlow g hr hnorm hsec hCcl hconv p ℓ
    hmaps).min_le_of_mem_Icc (left_mem_Icc.2 hℓ) (right_mem_Icc.2 hℓ) ht

/-- **Relative B5.1**: superlevel sets of `d(·, B)` in the closed totally convex `C` are totally
convex (`3 ≤ r`, `sec ≥ 0`, any dimension). -/
theorem isTotallyConvexFinite_superlevel_infDist_relBoundaryOfOrder [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) (a : ℝ) :
    IsTotallyConvexFinite g {x ∈ C | a ≤ infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C)} := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  intro p ℓ hℓ hp hpℓ t ht
  have hmaps : ∀ s ∈ Icc 0 ℓ, (g.geodesicFlow p s).proj ∈ C := hconv p ℓ hℓ hp.1 hpℓ.1
  refine ⟨hmaps t ht, ?_⟩
  have hmin := min_le_infDist_relBoundaryOfOrder_geodesicFlow g hr hnorm hsec hCcl hconv p hℓ hmaps ht
  rw [g.geodesicFlow_zero hr1 p] at hmin
  exact le_trans (le_min hp.2 hpℓ.2) hmin

/-- In full relative dimension the relative boundary of a closed totally convex set is its
frontier. -/
theorem relBoundaryOfOrder_eq_frontier
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C)
    (hd : maxSliceDimOfOrder I (r : ℕ∞ω) C = Module.finrank ℝ E) :
    relBoundaryOfOrder I (r : ℕ∞ω) C = frontier C := by
  rw [relBoundaryOfOrder, maxSliceLocusOfOrder_eq_interior g hr hnorm hconv hd,
    hCcl.frontier_eq]

/-- In full relative dimension, the REL binding contains theorem A. -/
example [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C)
    (hd : maxSliceDimOfOrder I (r : ℕ∞ω) C = Module.finrank ℝ E) (p : TangentBundle I M) (ℓ : ℝ)
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ) (fun t => infDist (g.geodesicFlow p t).proj (frontier C)) := by
  have h := concaveOn_infDist_relBoundaryOfOrder_geodesicFlow g hr hnorm hsec hCcl hconv p ℓ hmaps
  rwa [relBoundaryOfOrder_eq_frontier g (le_trans (by norm_num) hr) hnorm hCcl hconv hd] at h

end DifferentialGeometry.Geometry.FiniteSoul

end
