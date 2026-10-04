import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveGeneralShift

/-!
# Consumers of A1 (general-dimension orthogonal boundary shift)

Lane CMS3-SHAVE, group 1.

* CMS-B's 2D theorem `exists_orthogonal_boundary_shift_dim_two`, verbatim signature, re-derived as an
  `example` from A1 `exists_orthogonal_boundary_shift_of_transverseShift` and CMS-J's supplier
  `exists_transverse_shift_lipschitz_dim_two`;
* `exists_orthogonal_boundary_shift_at_of_shift`: the shift at the base point itself (`y = x`), in any
  dimension, from the transverse-shift hypothesis.
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

/-- CMS-B's B3 `exists_orthogonal_boundary_shift_dim_two` (verbatim signature) from A1 + CMS-J. -/
example
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hC : IsTotallyConvexFinite g C)
    (hCcl : IsClosed C) {x : M} (hx : x ∈ interior C) :
    ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 → g.inner y w w = 1 →
      g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  exact exists_orthogonal_boundary_shift_of_transverseShift g (le_trans (by norm_num) hr) hnorm
    (exists_transverse_shift_lipschitz_dim_two g hr hnorm hsec hdim) hC hCcl hx

/-- **The orthogonal shift at the base point** (any dimension): if `u` points from `x ∈ int C` to a
nearest point of `∂C`, then moving from `x` orthogonally to `u` by less than `ρ` does not increase the
distance to `∂C`. -/
theorem exists_orthogonal_boundary_shift_at_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hshift : ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
      g.inner p.proj p.snd p.snd = 1 → ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂|)
    {C : Set M} (hC : IsTotallyConvexFinite g C) (hCcl : IsClosed C) {x : M} (hx : x ∈ interior C) :
    ∃ ρ > (0 : ℝ), ∀ u w : E, g.inner x u u = 1 → g.inner x w w = 1 → g.inner x u w = 0 →
      g.expMap (⟨x, infDist x (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨x, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist x (frontier C) := by
  obtain ⟨ρ, hρ, hsh⟩ :=
    exists_orthogonal_boundary_shift_of_transverseShift g hr hnorm hshift hC hCcl hx
  exact ⟨ρ, hρ, hsh x (by rw [dist_self]; exact hρ)⟩

end DifferentialGeometry.Geometry.FiniteSoul

end
