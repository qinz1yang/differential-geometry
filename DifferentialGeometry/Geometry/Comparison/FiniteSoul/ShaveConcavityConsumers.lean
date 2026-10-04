import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveConcavity

/-!
# Consumers of the boundary concavity (S-SHAVE group 2)

* the frozen S-SHAVE statement of `build-logs/scratch/D-CMS/FiniteSoulInterfaces.lean`, verbatim
  plus `hdim` (review correction D2), as an `example` derived from
  `concaveOn_infDist_frontier_geodesicFlow`;
* `min_le_infDist_frontier_geodesicFlow`: along a geodesic arc in `C`, the boundary distance is at
  least the smaller endpoint value (input of the superlevel-set convexity of group 3);
* `infDist_frontier_expMap_eq_of_foot`: the step `infDist_frontier_step` in the direction of the
  nearest boundary point is exact, `d(exp_x (h u), ∂C) = d(x, ∂C) - h`.
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

/-- The frozen S-SHAVE interface statement, verbatim (instance block included) plus `hdim`; the
unused `hint`, `hℓ` carry a `_` prefix. -/
example [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2)
    {C : Set M} (hCc : IsCompact C) (hconv : IsTotallyConvexFinite g C)
    (_hint : (interior C).Nonempty) (p : TangentBundle I M) (ℓ : ℝ) (_hℓ : 0 ≤ ℓ)
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ) (fun t => infDist (g.geodesicFlow p t).proj (frontier C)) :=
  concaveOn_infDist_frontier_geodesicFlow g hr hnorm hsec hdim hCc.isClosed hconv p ℓ hmaps

/-- **Minimum principle for the boundary distance** along a geodesic arc in `C` (surface). -/
theorem min_le_infDist_frontier_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCcl : IsClosed C)
    (hconv : IsTotallyConvexFinite g C) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) {t : ℝ} (ht : t ∈ Icc 0 ℓ) :
    min (infDist (g.geodesicFlow p 0).proj (frontier C))
        (infDist (g.geodesicFlow p ℓ).proj (frontier C)) ≤
      infDist (g.geodesicFlow p t).proj (frontier C) :=
  (concaveOn_infDist_frontier_geodesicFlow g hr hnorm hsec hdim hCcl hconv p ℓ hmaps).min_le_of_mem_Icc
    (left_mem_Icc.2 hℓ) (right_mem_Icc.2 hℓ) ht

/-- **The step towards the nearest boundary point is exact**: `d(exp_x (h u), ∂C) = d(x, ∂C) - h`
for `0 ≤ h ≤ d(x, ∂C)`; the step `infDist_frontier_step` with `e = u` is the upper half of this. -/
theorem infDist_frontier_expMap_eq_of_foot
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hC : IsTotallyConvexFinite g C)
    (hCcl : IsClosed C) {x : M} (hx : x ∈ interior C) {u : E} (hu : g.inner x u u = 1)
    (hfoot : g.expMap (⟨x, infDist x (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C) :
    (∀ h ∈ Icc 0 (infDist x (frontier C)),
      infDist (g.expMap (⟨x, h • u⟩ : TangentBundle I M)) (frontier C) =
        infDist x (frontier C) - h) ∧
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • u⟩ : TangentBundle I M)) (frontier C) ≤
      infDist x (frontier C) - h * g.inner x u u :=
  ⟨fun h hh => ((dist_infDist_expMap_smul_of_foot g (le_trans (by norm_num) hr) hnorm hu hfoot).2
      h hh).2,
    infDist_frontier_step g hr hnorm hsec hdim hC hCcl hx hu hfoot hu⟩

end DifferentialGeometry.Geometry.FiniteSoul

end
