import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Convexity of small balls (MSM135 `lbl417`)

The assembly promised in `GeodesicConvexity.lean`: small intrinsic-distance
balls are geodesically convex, given the two analytic inputs named there —

1. a two-point joining selector `join` (continuity and endpoints; the
   minimising-geodesic selector of the Hopf–Rinow family), and
2. the convexity of `t ↦ d(O, join a b t)²` along the joining curves (the
   scalar along-curve form of the book's `lbl416`, "local convexity of the
   distance squared function", which follows from the `lbl413` Hessian
   comparison — the plan-approved honest-input boundary).

The proof is the book's max-principle argument for `lbl417`: a convex function
on `[0,1]` is at most the max of its endpoint values, so
`d(O, join a b t)² ≤ max{d(O,a)², d(O,b)²} < r²` and the joining curve never
leaves the ball.  Finiteness of `riemannianEDist` is automatic on a connected
manifold (`riemannianEDist_ne_top`), so no finiteness input is needed.

The radius bootstrap (the joining curve a priori lives in `B(O,3r)`, so the
`lbl416` input is needed there; the Step A wiring uses radii `< π/(6√C₀)` to
leave that slack — chapter4 L1346) belongs to the input *producer*, not to this
assembly.  See `ConvexBalls.md` for the item-3 brick plan.
-/

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

/-- **MSM135 `lbl417` (Convexity of small enough balls), assembly form.**

Given a joining selector `join` whose curves between ball points are continuous
with the right endpoints, and the `lbl416` input that the squared distance to
the centre is convex along each joining curve, the small intrinsic ball
`smallNormalBall O r` is geodesically convex for `join`.

The two hypotheses are exactly the two analytic inputs named in
`GeodesicConvexity.lean`: the minimising selector (Hopf–Rinow side) and the
Hessian positivity of `½ d(O,·)²` (second-variation side, via the `lbl413`
honest-input comparison). -/
theorem isConvexWith_smallNormalBall
    (join : M → M → ℝ → M) (O : M) {r : ℝ}
    (hjoin : ∀ a ∈ smallNormalBall (I := I) O r, ∀ b ∈ smallNormalBall (I := I) O r,
      ContinuousOn (join a b) unitInterval ∧ join a b 0 = a ∧ join a b 1 = b)
    (hconv : ∀ a ∈ smallNormalBall (I := I) O r, ∀ b ∈ smallNormalBall (I := I) O r,
      ConvexOn ℝ unitInterval
        (fun t => (riemannianEDist I O (join a b t)).toReal ^ 2)) :
    IsGeodesicallyConvexWith join (smallNormalBall (I := I) O r) := by
  intro a ha b hb
  obtain ⟨hcont, h0, h1⟩ := hjoin a ha b hb
  refine ⟨hcont, h0, h1, fun t ht => ?_⟩
  have hane : riemannianEDist I O a ≠ ⊤ := riemannianEDist_ne_top (I := I) O a
  have hbne : riemannianEDist I O b ≠ ⊤ := riemannianEDist_ne_top (I := I) O b
  have hta : (riemannianEDist I O a).toReal < r :=
    (ENNReal.lt_ofReal_iff_toReal_lt hane).mp ha
  have htb : (riemannianEDist I O b).toReal < r :=
    (ENNReal.lt_ofReal_iff_toReal_lt hbne).mp hb
  -- the convex function `t ↦ d(O, join a b t)²` is at most its endpoint max
  have hseg : t ∈ segment ℝ (0 : ℝ) (1 : ℝ) := by
    rw [segment_eq_Icc zero_le_one]; exact ht
  have hmax := (hconv a ha b hb).le_on_segment
    unitInterval.zero_mem unitInterval.one_mem hseg
  rw [h0, h1] at hmax
  -- endpoint values are `< r²`, and `toReal` is nonnegative
  have htR : (0 : ℝ) ≤ (riemannianEDist I O (join a b t)).toReal :=
    ENNReal.toReal_nonneg
  have htaR : (0 : ℝ) ≤ (riemannianEDist I O a).toReal := ENNReal.toReal_nonneg
  have htbR : (0 : ℝ) ≤ (riemannianEDist I O b).toReal := ENNReal.toReal_nonneg
  have hlt : (riemannianEDist I O (join a b t)).toReal < r := by
    rcases le_max_iff.mp hmax with hcase | hcase <;> nlinarith
  exact (ENNReal.lt_ofReal_iff_toReal_lt
    (riemannianEDist_ne_top (I := I) O (join a b t))).mpr hlt

end Riemannian
end Geometry
end DifferentialGeometry
