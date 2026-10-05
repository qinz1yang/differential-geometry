import DifferentialGeometry.Geometry.Comparison.FiniteMetric.GlobalComparison
import DifferentialGeometry.Geometry.Metric.Approximation.RayConeLimitProperties

/-!
# LFR59 for the finite model: the cone package of a finite-order metric with `sec ≥ 0`

Frozen blueprint master207A, LFR49 (A:29096): "Supply LC21's cone package for the SAME limit,
using the point cone in the compact case". The limit of LFR14 carries only a `C^{K-1}` metric.
Its cone package comes from metric comparison geometry alone:

* the finite global four-point comparison `fourPointComparison_zero_univ_finite` (sec ≥ 0, order
  at least two, complete);
* metric segments from the finite approximate midpoints `approximate_midpoints_finite`;
* the metric cone at infinity `exists_cone_at_infinity_package_of_fourPointComparison_zero`
  (TITS-T1–T4; it returns the point cone when the space is bounded).

`exists_finite_cone_package` is the result (statement T1 of lane LFR49).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LFR59 for the finite model.** A proper complete finite-order (`C^{≥2}`) Riemannian manifold
with `sec ≥ 0` has an LC21 cone package at every point: AC82 radial data, proper, complete,
four-point comparison zero, and Kleiner–Lott `τ`-maps from every blow-down `(R⁻¹ N, q)`,
`R ≥ R₀(τ)` (the point cone in the bounded case). -/
theorem exists_finite_cone_package {N : Type u} [MetricSpace N] [ProperSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [SigmaCompactSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)]
    [IsRiemannianManifold I N] [CompleteSpace N] {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hsec : ∀ (y : N) (w₁ w₂ : TangentSpace I y), 0 ≤ G.sectionalCurvature y w₁ w₂) (q : N) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧ fourPointComparison 0 (univ : Set C) ∧
      ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox N C ((inferInstance : MetricSpace N).rescale R⁻¹
          (inv_pos.mpr hR)) mC q o τ) := by
  have hcomp := DifferentialGeometry.Geometry.FiniteComparison.fourPointComparison_zero_univ_finite
    G hn hGnorm hsec
  have hseg : ∀ a b : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := fun a b =>
    Metric.exists_metric_segment_of_approximate_midpoints
      (DifferentialGeometry.Geometry.FiniteComparison.approximate_midpoints_finite G hn hGnorm) a b
  obtain ⟨C, mC, o, hH, hp, hc, -, hcompC, -, hK⟩ :=
    exists_cone_at_infinity_package_of_fourPointComparison_zero hcomp hseg q
  exact ⟨C, mC, o, hH, hp, hc, hcompC, hK⟩

end DifferentialGeometry.Geometry.Collapse
