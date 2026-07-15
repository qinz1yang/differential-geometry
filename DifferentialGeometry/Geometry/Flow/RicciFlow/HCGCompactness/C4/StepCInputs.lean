import DifferentialGeometry.Geometry.Comparison.CenterOfMass

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step C inputs

This file records the book-cited strict Hessian/strict-convexity input used by
the center-of-mass step.  The general minimizer and uniqueness assembly lives in
`Geometry/Comparison/CenterOfMass.lean`; this C4 layer only names the exact
MSM135 `lbl413`/`lbl416` conclusion consumed there.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

/-- MSM135 `lbl413`/`lbl416` strict-convexity input for the Step-C center of mass.

The fields are exactly the geometric facts consumed by
`CenterOfMass.exists_unique_curve*`: the selected joining curve stays in the
closed `2r` ball at the midpoint, has the right endpoints, and every summand
`q ↦ 1/2 d(q, pts i)^2` is strictly convex along the joining curve. -/
structure StrictDistInput (g : SmoothRiemannianMetric I M)
    {ι : Type} [Fintype ι] (pts : ι → M)
    (join : M → M → ℝ → M) (p : M) (r : ℝ) : Prop where
  mid :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
      a ≠ b → join a b (1 / 2 : ℝ) ∈ Metric.closedBall p (2 * r)
  zero :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
      join a b 0 = a
  one :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
      join a b 1 = b
  strict :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ i : ι, ∀ a ∈ Metric.closedBall p (2 * r),
      ∀ b ∈ Metric.closedBall p (2 * r), a ≠ b →
        StrictConvexOn ℝ unitInterval
          (fun t : ℝ => CenterOfMass.halfSqDist (pts i) (join a b t))

end HCGCompactness
end DifferentialGeometry
