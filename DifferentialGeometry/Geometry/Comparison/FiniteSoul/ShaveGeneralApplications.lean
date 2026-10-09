import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveGeneralShift
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveGeneralConcavity

/-!
# Consumers of A1 + A2 (general-dimension top shave)

Lane CMS3-SHAVE, group 2.

* CMS-B's 2D theorem B4.5 `concaveOn_infDist_frontier_geodesicFlow`, verbatim signature, re-derived as
  an `example` from A2 `concaveOn_infDist_frontier_of_orthogonalShift`, A1
  `exists_orthogonal_boundary_shift_of_transverseShift` and CMS-J's supplier
  `exists_transverse_shift_lipschitz_dim_two`;
* `concaveOn_infDist_frontier_of_transverseShift`: A1 + A2 in one step, from the transverse-shift
  hypothesis (the output shape of S3-SHIFT) to the concavity of `d(·, ∂C)` along arcs of `C`, in any
  dimension (the general-dimension S-SHAVE with its only dimension-dependent input inline);
* `min_le_infDist_frontier_geodesicFlow_of_shift`: the minimum principle for `d(·, ∂C)` along a geodesic
  arc in `C`, in any dimension (input of the superlevel-set convexity of the dimension drop).
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

/-- CMS-B's B4.5 `concaveOn_infDist_frontier_geodesicFlow` (verbatim signature) from A1 + A2 + CMS-J. -/
example
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCcl : IsClosed C)
    (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M) (ℓ : ℝ)
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ) (fun t => infDist (g.geodesicFlow p t).proj (frontier C)) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  exact concaveOn_infDist_frontier_of_orthogonalShift g hr2 hnorm hsec hconv
    (fun x hx => exists_orthogonal_boundary_shift_of_transverseShift g hr2 hnorm
      (exists_transverse_shift_lipschitz_dim_two g hr hnorm hsec hdim) hconv hCcl hx) p ℓ hmaps

/-- **General-dimension S-SHAVE with the transverse shift inline** (A1 + A2): if unit geodesics carry
unit normal fields with `1`-Lipschitz shifted curves (`hshift`, the output shape of S3-SHIFT and of
CMS-J's 2D supplier), then `d(·, ∂C)` is concave along every geodesic arc of the closed totally convex
set `C`. -/
theorem concaveOn_infDist_frontier_of_transverseShift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hshift : ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
      g.inner p.proj p.snd p.snd = 1 → ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂|)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M)
    (ℓ : ℝ) (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ) (fun t => infDist (g.geodesicFlow p t).proj (frontier C)) :=
  concaveOn_infDist_frontier_of_orthogonalShift g hr hnorm hsec hconv
    (fun _ hx => exists_orthogonal_boundary_shift_of_transverseShift g hr hnorm hshift hconv hCcl hx)
    p ℓ hmaps

/-- **Minimum principle for the boundary distance** along a geodesic arc in `C`, any dimension, from
the transverse-shift hypothesis. -/
theorem min_le_infDist_frontier_geodesicFlow_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hshift : ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
      g.inner p.proj p.snd p.snd = 1 → ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂|)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) {t : ℝ}
    (ht : t ∈ Icc 0 ℓ) :
    min (infDist (g.geodesicFlow p 0).proj (frontier C))
        (infDist (g.geodesicFlow p ℓ).proj (frontier C)) ≤
      infDist (g.geodesicFlow p t).proj (frontier C) :=
  (concaveOn_infDist_frontier_of_transverseShift g hr hnorm hsec hshift hCcl hconv p ℓ
    hmaps).min_le_of_mem_Icc (left_mem_Icc.2 hℓ) (right_mem_Icc.2 hℓ) ht

end DifferentialGeometry.Geometry.FiniteSoul

end
