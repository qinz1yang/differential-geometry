import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorus
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.DistancePullback

/-!
# The flat metric of the lattice torus and its exact distance bounds (S-FIXTURE-C1, K1, file 2)

* `torMetric_FXC1 Λ`: the smooth Riemannian metric on `T³_Λ` whose pullback along the covering map
  `torPi_FXC1` is the Euclidean metric of `ℝ³` (descent: `exists_unique_metric_of_surjective_
  localDiffeomorph`, the translations preserve the Euclidean metric);
* `torMS_FXC1 Λ`: the induced length metric space (`dist` is the Riemannian distance, `hmetric` by
  `inducedMetricSpace_hmetric`, as for the dihedral fixture);
* `edist_torPi_le_FXC1`: `d(π x, π y) ≤ ‖x - y‖` (the covering map does not increase distance);
* `le_edist_torPi_FXC1`: if every lift `y + v` of `π y` is at least `r` away from `x` then
  `r ≤ d(π x, π y)` (path lifting through the covering map,
  `le_edistOf_of_coveringMap_localPullMetric`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- Lattice translations are isometries of the Euclidean metric. -/
theorem pullback_euclideanMetric_smul_FXC1 (Λ : TorusPeriods_FXC1) (n : TorusGroup_FXC1 Λ) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := E3))
      (MulAction.smulDiffeomorph (n := ∞) 𝓘(ℝ, E3) n) = euclideanMetric (E := E3) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  have hd : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (MulAction.smulDiffeomorph (n := ∞) 𝓘(ℝ, E3) n) x =
      ContinuousLinearMap.id ℝ E3 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun y : E3 => y + latticeVec_FXC1 Λ n) x = _
    exact ((hasFDerivAt_id x).add_const (latticeVec_FXC1 Λ n)).fderiv
  rw [hd]
  rfl

/-- **The flat metric of the torus**: descent of the Euclidean metric along the covering map. -/
theorem exists_torMetric_FXC1 (Λ : TorusPeriods_FXC1) :
    ∃! h : SmoothRiemannianMetric 𝓘(ℝ, E3) (Tor_FXC1 Λ),
      localPullMetric h (torPi_FXC1 Λ) (torPi_isLocalDiffeomorph_FXC1 Λ) =
        euclideanMetric (E := E3) :=
  exists_unique_metric_of_surjective_localDiffeomorph (euclideanMetric (E := E3)) (torPi_FXC1 Λ)
    (torPi_isLocalDiffeomorph_FXC1 Λ) (torPi_surjective_FXC1 Λ)
    (metricFiberCompatible_quotientMk_of_invariant (euclideanMetric (E := E3))
      (pullback_euclideanMetric_smul_FXC1 Λ))

/-- The flat metric of the torus `ℝ³ / Λ`. -/
def torMetric_FXC1 (Λ : TorusPeriods_FXC1) : SmoothRiemannianMetric 𝓘(ℝ, E3) (Tor_FXC1 Λ) :=
  (exists_torMetric_FXC1 Λ).exists.choose

theorem torMetric_localPull_FXC1 (Λ : TorusPeriods_FXC1) :
    localPullMetric (torMetric_FXC1 Λ) (torPi_FXC1 Λ) (torPi_isLocalDiffeomorph_FXC1 Λ) =
      euclideanMetric (E := E3) :=
  (exists_torMetric_FXC1 Λ).exists.choose_spec

/-- The induced length metric space of the flat torus (not an instance). -/
@[reducible] def torMS_FXC1 (Λ : TorusPeriods_FXC1) : MetricSpace (Tor_FXC1 Λ) :=
  inducedMetricSpace (torMetric_FXC1 Λ)

theorem torMS_hmetric_FXC1 (Λ : TorusPeriods_FXC1) :
    letI := torMS_FXC1 Λ
    ∀ a b : Tor_FXC1 Λ,
      riemannianEDistOf (torMetric_FXC1 Λ) a b = ENNReal.ofReal (dist a b) :=
  inducedMetricSpace_hmetric (torMetric_FXC1 Λ)

theorem riemannianEDistOf_euclid_FXC1 (x y : E3) :
    riemannianEDistOf (euclideanMetric (E := E3)) x y = ENNReal.ofReal ‖x - y‖ := by
  have h := Geometry.riemannianEDistOf_standardEuclideanMetric x y
  rw [edist_dist, dist_eq_norm] at h
  exact h

/-- The covering map does not increase the Riemannian distance. -/
theorem edist_torPi_le_FXC1 (Λ : TorusPeriods_FXC1) (x y : E3) :
    riemannianEDistOf (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) (torPi_FXC1 Λ y) ≤
      ENNReal.ofReal ‖x - y‖ := by
  have h := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph (euclideanMetric (E := E3))
    (torMetric_FXC1 Λ) (torPi_FXC1 Λ) (torPi_isLocalDiffeomorph_FXC1 Λ) (c := 1) one_pos
    (fun x v => by
      have h1 := localPullMetric_inner (torMetric_FXC1 Λ) (torPi_FXC1 Λ)
        (torPi_isLocalDiffeomorph_FXC1 Λ) x v v
      rw [torMetric_localPull_FXC1] at h1
      rw [← h1, one_mul]) x y
  rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul, riemannianEDistOf_euclid_FXC1] at h
  exact h

/-- **Path lifting lower bound.** If every lift of `π y` is at least `r` away from `x`, then
`π x` and `π y` are at least `r` apart. -/
theorem le_edist_torPi_FXC1 (Λ : TorusPeriods_FXC1) (x y : E3) (r : ℝ)
    (h : ∀ n : TorusGroup_FXC1 Λ, r ≤ ‖x - (y + latticeVec_FXC1 Λ n)‖) :
    ENNReal.ofReal r ≤ riemannianEDistOf (torMetric_FXC1 Λ) (torPi_FXC1 Λ x) (torPi_FXC1 Λ y) := by
  refine le_edistOf_of_coveringMap_localPullMetric (euclideanMetric (E := E3))
    (torMetric_FXC1 Λ) (torPi_isLocalDiffeomorph_FXC1 Λ) (torPi_isCoveringMap_FXC1 Λ)
    (torMetric_localPull_FXC1 Λ) x (torPi_FXC1 Λ y) fun x' hx' => ?_
  obtain ⟨n, hn⟩ := torPi_eq_iff_FXC1.mp hx'.symm
  rw [riemannianEDistOf_euclid_FXC1, hn]
  exact ENNReal.ofReal_le_ofReal (h n)

end DifferentialGeometry.Geometry.Collapse
