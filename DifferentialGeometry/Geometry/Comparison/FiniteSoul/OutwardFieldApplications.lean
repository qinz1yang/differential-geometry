import DifferentialGeometry.Geometry.Comparison.FiniteSoul.OutwardFieldTwoTargets

/-!
# Consumers of POINT (lane CMS3-FLOW, G2)

* The frozen statement, verbatim, as an `example`.
* `exists_outward_field_point_margin_finite`: the LFR46.2 shape — a smooth field of `g`-length `≤ 2`,
  vanishing on `B̄(p, A₀) ⊇ S`, with margin `−1/4` against every unit minimizing direction to `p` at
  every `q` with `d(p, q) ≥ A₁` (the point family of POINT).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The frozen POINT statement, verbatim. -/
example [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p : M) {S : Set M} (hSc : IsCompact S) :
    ∃ A₀ A₁ : ℝ, 0 < A₀ ∧ A₀ < A₁ ∧ S ⊆ ball p A₀ ∧ ∃ Xf : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, Xf x⟩ : TangentBundle I M)) ∧
      (∀ q, g.inner q (Xf q) (Xf q) < 4) ∧ (∀ q, dist p q ≤ A₀ → Xf q = 0) ∧
      ∀ q, A₁ ≤ dist p q →
        ∀ v ∈ g.finiteMinimizingDirectionsTo {p} q ∪ g.finiteMinimizingDirectionsTo S q,
          g.inner q (Xf q) v ≤ -(1 / 4) :=
  exists_outward_field_two_targets_finite g hr hnorm hsec p hSc

/-- **The point margin (LFR46.2 shape).** -/
theorem exists_outward_field_point_margin_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p : M) {S : Set M} (hSc : IsCompact S) :
    ∃ A₀ A₁ : ℝ, 0 < A₀ ∧ A₀ < A₁ ∧ S ⊆ ball p A₀ ∧ ∃ Xf : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, Xf x⟩ : TangentBundle I M)) ∧
      (∀ q, Real.sqrt (g.inner q (Xf q) (Xf q)) ≤ 2) ∧ (∀ q, dist p q ≤ A₀ → Xf q = 0) ∧
      ∀ q, A₁ ≤ dist p q → ∀ u ∈ g.finiteMinimizingDirectionsTo {p} q,
        g.inner q (Xf q) u ≤ -(1 / 4) := by
  obtain ⟨A₀, A₁, hA₀, hA₀₁, hS, Xf, hXs, hX4, hX0, hXout⟩ :=
    exists_outward_field_two_targets_finite g hr hnorm hsec p hSc
  refine ⟨A₀, A₁, hA₀, hA₀₁, hS, Xf, hXs, fun q => ?_, hX0, fun q hq u hu =>
    hXout q hq u (Or.inl hu)⟩
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt (hX4 q).le

end DifferentialGeometry.Geometry.FiniteSoul
