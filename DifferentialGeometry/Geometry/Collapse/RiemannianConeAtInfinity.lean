import DifferentialGeometry.Geometry.Metric.Approximation.RayConeLimitProperties
import DifferentialGeometry.Geometry.Collapse.CompleteRiemannianSegments
import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint

/-!
# The full LC21 package for complete Riemannian manifolds with `sec ≥ 0`

Riemannian binding of tier T4 of the Tits-cone producer (LC21, A:20789; LFR59, A:29862). Let `M`
carry a metric space structure whose distance is the length distance of a smooth Riemannian metric
`g` (`hmetric`), complete, with `sec_g ≥ 0` everywhere. Then

* `M` is proper (Hopf–Rinow: `isCompact_riemannianClosedBallOf`),
* `M` has constant-speed minimizing segments (`segments_of_riemannianEDistOf_eq`, lane W4-F7d2),
* `M` has nonnegative four-point comparison on all of `M`
  (`fourPointComparison_zero_univ_of_sectional_nonneg`, from the eight-ball theorem
  `fourPointComparison_of_sectional_lower_bound_on_eight_ball` on a ball containing the four points),

so the package `exists_cone_at_infinity_package_of_fourPointComparison_zero` applies:
`exists_cone_at_infinity_package_of_sectional_nonneg` gives a cone at infinity that is proper,
complete, geodesic, nonnegatively curved in the four-point sense, of Hausdorff dimension at most
`dimH M`, with Kleiner–Lott maps from every large blow-down. Noncompactness of `M` is not assumed
(a compact `M` gets the one-point cone). The bound by `finrank ℝ E` is in
`DifferentialGeometry.Geometry.Collapse.RiemannianConeAtInfinityDimension`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- A complete manifold whose distance is the length distance of `g` is proper (Hopf–Rinow). -/
theorem properSpace_of_riemannianEDistOf_eq {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b)) :
    ProperSpace M := by
  have hg : RiemannianMetricComplete (I := I) g :=
    (riemannianMetricComplete_iff_completeSpace hmetric).mpr inferInstance
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun p r hr => ?_
  have heq : Metric.closedBall p r = riemannianClosedBallOf g p r := by
    ext y
    rw [Metric.mem_closedBall, dist_comm]
    change dist p y ≤ r ↔ riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal r
    rw [hmetric, ENNReal.ofReal_le_ofReal_iff hr]
  rw [heq]
  exact isCompact_riemannianClosedBallOf hg p r

/-- `sec_g ≥ 0` everywhere gives nonnegative four-point comparison on the whole manifold. -/
theorem fourPointComparison_zero_univ_of_sectional_nonneg {M : Type*} [MetricSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hsec : ∀ y, SectionalBoundedBelowAt g y 0) :
    fourPointComparison 0 (univ : Set M) := by
  intro z _ a _ b _ c _ hax hbx hcx
  let R := 1 + dist a z + dist b z + dist c z
  have hz : z ∈ ball z R := by
    simp only [mem_ball, dist_self, R]
    positivity
  have ha : a ∈ ball z R := by
    simp only [mem_ball, R]
    linarith [dist_nonneg (x := b) (y := z), dist_nonneg (x := c) (y := z)]
  have hb : b ∈ ball z R := by
    simp only [mem_ball, R]
    linarith [dist_nonneg (x := a) (y := z), dist_nonneg (x := c) (y := z)]
  have hc : c ∈ ball z R := by
    simp only [mem_ball, R]
    linarith [dist_nonneg (x := a) (y := z), dist_nonneg (x := b) (y := z)]
  exact fourPointComparison_of_sectional_lower_bound_on_eight_ball g hmetric z le_rfl
    (fun y _ => by rw [neg_zero]; exact hsec y) z hz a ha b hb c hc hax hbx hcx

/-- The full LC21 package for a complete Riemannian manifold with `sec ≥ 0`: a cone at infinity,
fixed before `ε`, with AC82 radial data, proper, complete, geodesic, with nonnegative four-point
comparison and `dimH C ≤ dimH M`, and Kleiner–Lott `ε`-maps from every blow-down `(R⁻¹ M, p)`,
`R ≥ R₀(ε)`. -/
theorem exists_cone_at_infinity_package_of_sectional_nonneg {M : Type u} [mM : MetricSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hsec : ∀ y, SectionalBoundedBelowAt g y 0) (p : M) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧
      (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      fourPointComparison 0 (univ : Set C) ∧ dimH (univ : Set C) ≤ dimH (univ : Set M) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox M C (mM.rescale R⁻¹ (inv_pos.mpr hR)) mC p o ε) := by
  have := properSpace_of_riemannianEDistOf_eq g hmetric
  exact exists_cone_at_infinity_package_of_fourPointComparison_zero
    (fourPointComparison_zero_univ_of_sectional_nonneg g hmetric hsec)
    (segments_of_riemannianEDistOf_eq g hmetric) p

end DifferentialGeometry.Geometry.Collapse
