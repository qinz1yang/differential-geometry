import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveMaximalSet
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RayExhaustionConvex

/-!
# Consumers of the shaving step (S-SHAVE group 3)

`shave_rayExhaustion_sublevel_dim_two`: on a connected noncompact complete surface with `sec ≥ 0`,
the first shave of a nonempty flag set `C_t = {rayExhaustion o ≤ t}` of LFR21 (lane CMS-A,
`isCompact_isTotallyConvexFinite_rayExhaustion_sublevel`): `∂C_t ≠ ∅` (Mathlib's
`nonempty_frontier_iff`, since `C_t` is compact and `M` is not), and the maximal set of
`d(·, ∂C_t)` on `C_t` is compact, nonempty, totally convex, inside `C_t`, with empty interior
(`isCompact_isTotallyConvexFinite_argmax_infDist_frontier`). The frozen concavity statement itself
is consumed verbatim in `ShaveConcavityConsumers.lean`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (rayExhaustion)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The first shave of a flag set `C_t` on a connected noncompact surface** (`sec ≥ 0`). -/
theorem shave_rayExhaustion_sublevel_dim_two [ConnectedSpace M] [NoncompactSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (o : M) {t : ℝ}
    (hne : {x : M | rayExhaustion o x ≤ t}.Nonempty) :
    (frontier {x : M | rayExhaustion o x ≤ t}).Nonempty ∧
      IsCompact {x ∈ {x : M | rayExhaustion o x ≤ t} | ∀ y ∈ {x : M | rayExhaustion o x ≤ t},
        infDist y (frontier {x : M | rayExhaustion o x ≤ t}) ≤
          infDist x (frontier {x : M | rayExhaustion o x ≤ t})} ∧
      {x ∈ {x : M | rayExhaustion o x ≤ t} | ∀ y ∈ {x : M | rayExhaustion o x ≤ t},
        infDist y (frontier {x : M | rayExhaustion o x ≤ t}) ≤
          infDist x (frontier {x : M | rayExhaustion o x ≤ t})}.Nonempty ∧
      IsTotallyConvexFinite g {x ∈ {x : M | rayExhaustion o x ≤ t} |
        ∀ y ∈ {x : M | rayExhaustion o x ≤ t},
          infDist y (frontier {x : M | rayExhaustion o x ≤ t}) ≤
            infDist x (frontier {x : M | rayExhaustion o x ≤ t})} ∧
      {x ∈ {x : M | rayExhaustion o x ≤ t} | ∀ y ∈ {x : M | rayExhaustion o x ≤ t},
        infDist y (frontier {x : M | rayExhaustion o x ≤ t}) ≤
          infDist x (frontier {x : M | rayExhaustion o x ≤ t})} ⊆ {x : M | rayExhaustion o x ≤ t} ∧
      interior {x ∈ {x : M | rayExhaustion o x ≤ t} | ∀ y ∈ {x : M | rayExhaustion o x ≤ t},
        infDist y (frontier {x : M | rayExhaustion o x ≤ t}) ≤
          infDist x (frontier {x : M | rayExhaustion o x ≤ t})} = ∅ := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have : SigmaCompactSpace M := inferInstance
  obtain ⟨hCc, hconv⟩ :=
    isCompact_isTotallyConvexFinite_rayExhaustion_sublevel g (le_trans (by norm_num) hr) hnorm hsec o t
  have hB := nonempty_frontier_iff.2 ⟨hne, hCc.ne_univ⟩
  exact ⟨hB, isCompact_isTotallyConvexFinite_argmax_infDist_frontier g hr hnorm hsec hdim hCc hne
    hconv hB⟩

end DifferentialGeometry.Geometry.FiniteSoul

end
