import DifferentialGeometry.Geometry.Collapse.FixtureCT.KleinCarrier
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Collapse.FixtureC1.LatticeTorusMetric

/-!
# The flat metric of the edge carrier `S¹_a × K_{b,L}` (lane O-FIXTURE-CT, K-C, file 2)

* `inner_kleinLin_OFT`: the linear part `diag(1, ±1, 1)` of every group element is a linear
  isometry;
* `pullback_euclideanMetric_smul_OFT`: the group acts by isometries of the Euclidean metric;
* `kleinMetric_OFT P`: the descended flat metric (`exists_unique_metric_of_surjective_
  localDiffeomorph`), `kleinMS_OFT P` the induced length metric space (not an instance) with
  `kleinMS_hmetric_OFT`;
* `edist_kleinPi_le_OFT`: `d(π x, π y) ≤ ‖x - y‖`; `le_edist_kleinPi_OFT`: if every lift `g • y`
  of `π y` is at least `r` away from `x` then `r ≤ d(π x, π y)` (path lifting through the covering
  map, `le_edistOf_of_coveringMap_localPullMetric`), as for the lattice torus of fixture C1.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The linear part of a group element preserves the Euclidean inner product. -/
theorem inner_kleinLin_OFT (k : ℤ) (v w : E3) :
    inner ℝ (kleinLin_OFT k v) (kleinLin_OFT k w) = inner ℝ v w := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [kleinLin_apply_OFT, PiLp.toLp_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, RCLike.inner_apply, conj_trivial]
  have h := kSign_real_mul_self_OFT k
  linear_combination (w 1 * v 1) * h

/-- The group acts by isometries of the Euclidean metric. -/
theorem pullback_euclideanMetric_smul_OFT (P : KleinPeriods_OFT) (g : KleinGroup_OFT P) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := E3))
      (MulAction.smulDiffeomorph (n := ∞) 𝓘(ℝ, E3) g) = euclideanMetric (E := E3) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  have hd : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (MulAction.smulDiffeomorph (n := ∞) 𝓘(ℝ, E3) g) x =
      kleinLin_OFT g.k := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun y : E3 => kleinLin_OFT g.k y + kleinVec_OFT P g) x = _
    exact ((kleinLin_OFT g.k).hasFDerivAt.add_const (kleinVec_OFT P g)).fderiv
  rw [hd, euclideanMetric_inner, euclideanMetric_inner]
  exact inner_kleinLin_OFT g.k v w

/-- **The flat metric of the edge carrier**: descent of the Euclidean metric. -/
theorem exists_kleinMetric_OFT (P : KleinPeriods_OFT) :
    ∃! h : SmoothRiemannianMetric 𝓘(ℝ, E3) (Klein_OFT P),
      localPullMetric h (kleinPi_OFT P) (kleinPi_isLocalDiffeomorph_OFT P) =
        euclideanMetric (E := E3) :=
  exists_unique_metric_of_surjective_localDiffeomorph (euclideanMetric (E := E3)) (kleinPi_OFT P)
    (kleinPi_isLocalDiffeomorph_OFT P) (kleinPi_surjective_OFT P)
    (metricFiberCompatible_quotientMk_of_invariant (euclideanMetric (E := E3))
      (pullback_euclideanMetric_smul_OFT P))

/-- The flat metric of `S¹_a × K_{b,L}`. -/
def kleinMetric_OFT (P : KleinPeriods_OFT) : SmoothRiemannianMetric 𝓘(ℝ, E3) (Klein_OFT P) :=
  (exists_kleinMetric_OFT P).exists.choose

theorem kleinMetric_localPull_OFT (P : KleinPeriods_OFT) :
    localPullMetric (kleinMetric_OFT P) (kleinPi_OFT P) (kleinPi_isLocalDiffeomorph_OFT P) =
      euclideanMetric (E := E3) :=
  (exists_kleinMetric_OFT P).exists.choose_spec

/-- The induced length metric space of the edge carrier (not an instance). -/
@[reducible] def kleinMS_OFT (P : KleinPeriods_OFT) : MetricSpace (Klein_OFT P) :=
  inducedMetricSpace (kleinMetric_OFT P)

theorem kleinMS_hmetric_OFT (P : KleinPeriods_OFT) :
    letI := kleinMS_OFT P
    ∀ a b : Klein_OFT P,
      riemannianEDistOf (kleinMetric_OFT P) a b = ENNReal.ofReal (dist a b) :=
  inducedMetricSpace_hmetric (kleinMetric_OFT P)

/-- The covering map does not increase the Riemannian distance. -/
theorem edist_kleinPi_le_OFT (P : KleinPeriods_OFT) (x y : E3) :
    riemannianEDistOf (kleinMetric_OFT P) (kleinPi_OFT P x) (kleinPi_OFT P y) ≤
      ENNReal.ofReal ‖x - y‖ := by
  have h := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph (euclideanMetric (E := E3))
    (kleinMetric_OFT P) (kleinPi_OFT P) (kleinPi_isLocalDiffeomorph_OFT P) (c := 1) one_pos
    (fun x v => by
      have h1 := localPullMetric_inner (kleinMetric_OFT P) (kleinPi_OFT P)
        (kleinPi_isLocalDiffeomorph_OFT P) x v v
      rw [kleinMetric_localPull_OFT] at h1
      rw [← h1, one_mul]) x y
  rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul, riemannianEDistOf_euclid_FXC1] at h
  exact h

/-- **Path lifting lower bound.** If every lift `g • y` of `π y` is at least `r` away from `x`,
then `π x` and `π y` are at least `r` apart. -/
theorem le_edist_kleinPi_OFT (P : KleinPeriods_OFT) (x y : E3) (r : ℝ)
    (h : ∀ g : KleinGroup_OFT P, r ≤ ‖x - g • y‖) :
    ENNReal.ofReal r ≤
      riemannianEDistOf (kleinMetric_OFT P) (kleinPi_OFT P x) (kleinPi_OFT P y) := by
  refine le_edistOf_of_coveringMap_localPullMetric (euclideanMetric (E := E3))
    (kleinMetric_OFT P) (kleinPi_isLocalDiffeomorph_OFT P) (kleinPi_isCoveringMap_OFT P)
    (kleinMetric_localPull_OFT P) x (kleinPi_OFT P y) fun x' hx' => ?_
  obtain ⟨g, hg⟩ := kleinPi_eq_iff_OFT.mp hx'.symm
  rw [riemannianEDistOf_euclid_FXC1, hg]
  exact ENNReal.ofReal_le_ofReal (h g)

end DifferentialGeometry.Geometry.Collapse
