import DifferentialGeometry.Geometry.Collapse.RiemannianOutwardPoint
import DifferentialGeometry.Geometry.Comparison.AlmostOppositeAngleRadius
import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureHinge
import DifferentialGeometry.Geometry.Comparison.Soul.NoncriticalDistance
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# LC27: one outward direction opposes all inward directions

Blueprint 207A, LC27 (`thm:collapse-annular-directions`, A:21066–21137). On a complete Riemannian
manifold with `sec ≥ -κ²` on `B(p, 20 b)`, `κ b ≤ 1/3`, an actual pointed Kleiner–Lott `δ`-map
from `(M, p)` to an AC82 cone with
`δ < min {a/30, 1/(4b+20), a(1 - cos τ)/90}` gives, at every `q` with `a ≤ d(p,q) ≤ b`, a unit
vector `w_q` making angle greater than `π - τ` with every initial unit velocity of a minimizing
segment from `q` to `p`; these velocities have pairwise distance `< 4 sin(τ/2) < 2τ`, and `q`
is noncritical for `d_p`.

The set of initial unit velocities is the soul toolkit's `minimizingDirectionsTo g hEnorm {p} q`
(unit `v` whose geodesic reaches `p` at time `d(q,p)`); by
`exists_intrinsicGeodesic_eq_metric_segment` every minimizing segment is such a geodesic. The
local comparison input of the blueprint (AC02) is the proved Riemannian hinge theorem
`hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses`,
applied with the curvature parameter `k = 1/(3b) ≥ κ` (so `κ = 0` needs no limit); its lens
hypothesis is verified inside `B(p, 5b)`. The outward point is LC25
(`exists_riemannian_metric_segment` + `exists_outward_point_on_annulus`), the model estimate is
LC26.
-/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set Real
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [MetricSpace M]
  [SigmaCompactSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The tangent norm of the Riemannian bundle is the `g`-norm. -/
theorem norm_tangent_eq_sqrt_gInner {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm g) {q : M} (z : TangentSpace I q) :
    ‖z‖ = Real.sqrt (g.inner q z z) := by
  rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [MetricSpace M]
  [SigmaCompactSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- Tangent algebra of LC27: two unit vectors that each make angle greater than `π - τ` with a
common unit vector `w` are at `g`-distance less than `4 sin (τ/2)`. -/
theorem sqrt_gInner_sub_lt_of_angle_gt {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm g) {q : M}
    {v v' w : TangentSpace I q} (hv : g.inner q v v = 1) (hv' : g.inner q v' v' = 1)
    (hw : g.inner q w w = 1) {τ : ℝ} (hτ : 0 < τ) (hτπ : τ ≤ π)
    (h : π - τ < Real.arccos (g.inner q v w)) (h' : π - τ < Real.arccos (g.inner q v' w)) :
    Real.sqrt (g.inner q (v - v') (v - v')) < 4 * Real.sin (τ / 2) := by
  have hsin : 0 < Real.sin (τ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcos : Real.cos τ = 1 - 2 * Real.sin (τ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (τ / 2)
    rw [show 2 * (τ / 2) = τ by ring] at h2
    nlinarith [Real.sin_sq_add_cos_sq (τ / 2)]
  have hlt (u : TangentSpace I q) (hu : g.inner q u u = 1)
      (hu' : π - τ < Real.arccos (g.inner q u w)) :
      Real.sqrt (g.inner q (u + w) (u + w)) < 2 * Real.sin (τ / 2) := by
    have hx : g.inner q u w < -Real.cos τ := by
      by_contra hx
      have hle := Real.arccos_le_arccos (le_of_not_gt hx)
      rw [Real.arccos_neg, Real.arccos_cos hτ.le hτπ] at hle
      linarith
    have hexp : g.inner q (u + w) (u + w) =
        g.inner q u u + 2 * g.inner q u w + g.inner q w w := by
      simp only [map_add, add_apply, g.symm q w u]
      ring
    rw [Real.sqrt_lt' (by positivity), hexp, hu, hw]
    nlinarith
  have htri : ‖v - v'‖ ≤ ‖v + w‖ + ‖v' + w‖ := by
    have hsplit : v - v' = (v + w) - (v' + w) := by abel
    rw [hsplit]
    exact norm_sub_le _ _
  rw [norm_tangent_eq_sqrt_gInner hEnorm, norm_tangent_eq_sqrt_gInner hEnorm,
    norm_tangent_eq_sqrt_gInner hEnorm] at htri
  linarith [hlt v hv h, hlt v' hv' h']

/-- LC27: one outward direction opposes all inward directions. -/
theorem exists_outward_unit_direction_of_kleinerLottApprox (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {C : Type*} [MetricSpace C] {o : C} {δ a b κ τ : ℝ}
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o) (ha : 0 < a) (hab : a ≤ b)
    (hκ : 0 ≤ κ) (hκb : κ * b ≤ 1 / 3)
    (hsec : ∀ y ∈ Metric.ball p (20 * b), SectionalBoundedBelowAt g y (-κ ^ 2))
    (hτ : 0 < τ) (hτπ : τ < π / 2) (hδa : δ < a / 30) (hδb : δ < 1 / (4 * b + 20))
    (hδτ : δ < a * (1 - Real.cos τ) / 90) {q : M} (hq : a ≤ dist p q ∧ dist p q ≤ b) :
    ∃ w : TangentSpace I q, g.inner q w w = 1 ∧
      (∀ v ∈ minimizingDirectionsTo g hEnorm {p} q, π - τ < Real.arccos (g.inner q v w)) ∧
      (∀ v ∈ minimizingDirectionsTo g hEnorm {p} q, g.inner q v w < 0) ∧
      (∀ v ∈ minimizingDirectionsTo g hEnorm {p} q, ∀ v' ∈ minimizingDirectionsTo g hEnorm {p} q,
        Real.sqrt (g.inner q (v - v') (v - v')) < 4 * Real.sin (τ / 2)) ∧
      4 * Real.sin (τ / 2) < 2 * τ := by
  set r := dist p q with hr_def
  have hr : 0 < r := ha.trans_le hq.1
  have hb : 0 < b := ha.trans_le hab
  have hδ := φ.error_pos
  obtain ⟨q', hq'2, hq'lo, hq'hi⟩ := φ.exists_outward_point_on_annulus H
    (exists_riemannian_metric_segment g hEnorm) ha hab (by linarith) hδb hq
  set ℓ := dist q q' with hℓ_def
  have hℓ : 0 < ℓ := hr.trans_le hq'lo
  obtain ⟨w, hw, hwend⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm q q'
    (by rw [toReal_riemannianEDist_eq_dist]; exact hℓ)
  rw [toReal_riemannianEDist_eq_dist] at hwend
  set k : ℝ := 1 / (3 * b) with hk_def
  have hk : 0 < k := by positivity
  have hκk : κ ≤ k := by
    rw [hk_def, le_div_iff₀ (by positivity)]
    linarith
  have hsq : -k ^ 2 ≤ -κ ^ 2 := by nlinarith
  have hkb : k * b ≤ 1 / 3 := by
    rw [hk_def]
    field_simp
    rfl
  set μ : ℝ := 15 * δ / a with hμ_def
  have hμ0 : 0 ≤ μ := by positivity
  have hμ1 : μ ≤ 1 := by
    rw [hμ_def, div_le_one ha]
    linarith
  have hμa : μ * a = 15 * δ := by
    rw [hμ_def]
    field_simp
  have hℓμ : ℓ ≤ (1 + μ) * r := by
    have h15 : 15 * δ ≤ μ * r := hμa ▸ mul_le_mul_of_nonneg_left hq.1 hμ0
    nlinarith
  have hbudget : 6 * μ < 1 - Real.cos τ := by
    rw [hμ_def, show 6 * (15 * δ / a) = 90 * δ / a by ring, div_lt_iff₀ ha]
    linarith
  have hmodel := (comparisonAngle_double_bounds_of_le_radius hk.le hr hq.2 hμ0 hμ1 hq'lo hℓμ
    hkb).2 τ hτ.le hbudget
  rw [comparisonAngleNegCurvature, ite_eq_right (pow_ne_zero 2 hk.ne'), Real.sqrt_sq hk.le] at hmodel
  have hmain : ∀ v ∈ minimizingDirectionsTo g hEnorm {p} q,
      π - τ < Real.arccos (g.inner q v w) := by
    intro v hv
    obtain ⟨hvu, hvend⟩ := hv
    rw [Metric.infDist_singleton, mem_singleton_iff, dist_comm] at hvend
    have hminA : (riemannianEDist I q (intrinsicGeodesic g hEnorm q v r)).toReal = r := by
      rw [hvend, toReal_riemannianEDist_eq_dist, dist_comm]
    have hminB : (riemannianEDist I q (intrinsicGeodesic g hEnorm q w ℓ)).toReal = ℓ := by
      rw [hwend, toReal_riemannianEDist_eq_dist]
    have hlens : ∀ s ∈ Icc (0 : ℝ) r, ∀ t ∈ Icc (0 : ℝ) ℓ, ∀ y : M,
        riemannianEDist I (intrinsicGeodesic g hEnorm q v s) y +
          riemannianEDist I y (intrinsicGeodesic g hEnorm q w t) =
          riemannianEDist I (intrinsicGeodesic g hEnorm q v s)
            (intrinsicGeodesic g hEnorm q w t) →
        SectionalBoundedBelowAt g y (-k ^ 2) := by
      intro s hs t ht y hy
      rw [← IsRiemannianManifold.out (I := I), ← IsRiemannianManifold.out (I := I),
        ← IsRiemannianManifold.out (I := I), edist_dist, edist_dist, edist_dist,
        ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
        ENNReal.ofReal_eq_ofReal_iff (add_nonneg dist_nonneg dist_nonneg) dist_nonneg] at hy
      have hP : dist q (intrinsicGeodesic g hEnorm q v s) ≤ s := by
        simpa only [intrinsicGeodesic_zero, hvu, Real.sqrt_one, one_mul, sub_zero] using
          dist_intrinsicGeodesic_le_mul g hEnorm q v hs.1
      have hQ : dist q (intrinsicGeodesic g hEnorm q w t) ≤ t := by
        simpa only [intrinsicGeodesic_zero, hw, Real.sqrt_one, one_mul, sub_zero] using
          dist_intrinsicGeodesic_le_mul g hEnorm q w ht.1
      refine SectionalBoundedBelowAt.mono (hsec y ?_) hsq
      rw [Metric.mem_ball, dist_comm]
      have h1 := dist_triangle p q (intrinsicGeodesic g hEnorm q v s)
      have h2 := dist_triangle p (intrinsicGeodesic g hEnorm q v s) y
      have h3 := dist_triangle (intrinsicGeodesic g hEnorm q v s) q
        (intrinsicGeodesic g hEnorm q w t)
      rw [dist_comm (intrinsicGeodesic g hEnorm q v s) q] at h3
      have hy0 := dist_nonneg (x := y) (y := intrinsicGeodesic g hEnorm q w t)
      nlinarith [hs.2, ht.2, hq.2]
    have h := hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses
      g hEnorm q v w hk hr hℓ hvu hw hminA hminB hlens
    rw [hvend, hwend, toReal_riemannianEDist_eq_dist, hq'2] at h
    exact hmodel.trans_le h
  refine ⟨w, hw, hmain, fun v hv => ?_, fun v hv v' hv' => ?_, ?_⟩
  · by_contra hcon
    have hle := Real.arccos_le_pi_div_two.mpr (le_of_not_gt hcon)
    linarith [hmain v hv]
  · exact sqrt_gInner_sub_lt_of_angle_gt hEnorm hv.1 hv'.1 hw hτ (by linarith [Real.pi_pos])
      (hmain v hv) (hmain v' hv')
  · have hs := Real.sin_lt (show 0 < τ / 2 by linarith)
    linarith

end DifferentialGeometry.Geometry.Collapse
