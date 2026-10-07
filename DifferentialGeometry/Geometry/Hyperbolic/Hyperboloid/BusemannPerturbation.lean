import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannHessian
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric
import DifferentialGeometry.Geometry.Metric.Convergence.FiniteOrderNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Connection.Convergence.PointwiseBound
import DifferentialGeometry.Geometry.Operator.Restriction

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Hyperboloid

section MetricBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metricDerivNorm_le_of_metricCkENormOn
    (g h : SmoothRiemannianMetric I M) {K : Set M} {p a : ℕ}
    (ha : a ≤ p) (ha' : a ≤ 1)
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h g g ≤ ENNReal.ofReal (1 / 100))
    {x : M} (hx : x ∈ K) :
    CheegerGromovCompactness.metricDerivNorm a h g g x ≤ 1 / 100 := by
  have hh := (CheegerGromovCompactness.weighted_metricDerivNorm_le_metricCkENormOn
    K p h g g ha hx).trans hsmall
  have haf : a.factorial = 1 := by interval_cases a <;> rfl
  rw [haf] at hh
  norm_num only [Nat.cast_one, inv_one, one_mul] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 100)).mp hh

private theorem quadratic_bounds_of_metricCkENormOn
    (g h : SmoothRiemannianMetric I M) {K : Set M} {p : ℕ}
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h g g ≤ ENNReal.ofReal (1 / 100))
    {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    (9 / 10 : ℝ) * g.inner x v v ≤ h.inner x v v ∧
      h.inner x v v ≤ (11 / 10 : ℝ) * g.inner x v v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hg : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (g.pos x v hv).le
  have hn := metricDerivNorm_le_of_metricCkENormOn g h (Nat.zero_le p) (by decide) hsmall hx
  have hd := CheegerGromovCompactness.metricDifference_abs_le h g g x v v
  rw [mul_assoc, Real.mul_self_sqrt hg] at hd
  have ha := hd.trans (mul_le_mul_of_nonneg_right hn hg)
  obtain ⟨hl, hu⟩ := abs_le.mp ha
  constructor <;> nlinarith only [hl, hu, hg]

private theorem connectionDifference_norm_le_of_metricCkENormOn
    (g h : SmoothRiemannianMetric I M) {K : Set M} {p : ℕ} (hp : 1 ≤ p)
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h g g ≤ ENNReal.ofReal (1 / 100))
    {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    let A := CovariantDerivative.difference
      (Geometry.Connection.LeviCivita h) (Geometry.Connection.LeviCivita g) x v v
    Real.sqrt (g.inner x A A) ≤ (5 / 243 : ℝ) * g.inner x v v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlow (z : TangentSpace I x) : (9 / 10 : ℝ) * g.inner x z z ≤ h.inner x z z :=
    (quadratic_bounds_of_metricCkENormOn g h hsmall hx z).1
  have hJet : CheegerGromovCompactness.MetricCovDerivOrderBoundOn K 1 h g (1 / 100) := by
    intro y hy
    have hn := metricDerivNorm_le_of_metricCkENormOn g h hp le_rfl hsmall hy
    have hc := CheegerGromovCompactness.covNorm_le_add 1 h g g y
    rw [CheegerGromovCompactness.covNorm_self_succ g 0 y, zero_add] at hc
    exact hc.trans hn
  have hb := Geometry.Connection.connectionDifference_norm_le_of_metric_lower_bound
    h g x (by norm_num : (0 : ℝ) < 9 / 10) hlow v v
  have hg : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (g.pos x v hv).le
  dsimp only at hb
  rw [mul_assoc, Real.mul_self_sqrt hg] at hb
  have hsmall' := hJet x hx
  calc
    _ ≤ (3 / (2 * (9 / 10 : ℝ))) *
        CheegerGromovCompactness.metricCovDerivNorm 1 h g x * g.inner x v v := hb
    _ ≤ (3 / (2 * (9 / 10 : ℝ))) * (1 / 100) * g.inner x v v := by
      gcongr
    _ ≤ _ := by nlinarith only [hg]

end MetricBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem hessFun_two_mul_log_time_sub_inner_restrictOpen
    (U : TopologicalSpace.Opens (Hyperboloid E)) (ξ : Metric.sphere (0 : E) 1)
    (x : U) (v w : TangentSpace 𝓘(ℝ, E) x) :
    let g := (scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U
    let ρ := fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)
    Geometry.Operator.hessFun g ρ x v w =
      (1 / 2 : ℝ) * (g.inner x v w - mvfderiv 𝓘(ℝ, E) ρ x v * mvfderiv 𝓘(ℝ, E) ρ x w) := by
  let F := fun y : Hyperboloid E => 2 * Real.log (y.time - inner ℝ (ξ : E) y.space)
  have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ F :=
    contMDiff_const.mul (contMDiff_log_time_sub_inner ξ)
  dsimp only
  rw [Geometry.Operator.hessFun_restrictOpen_of_contMDiff _ U F hF,
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
  rw [Geometry.Curvature.mvfderiv_restrictOpen U F x v (hF.mdifferentiableAt (by simp)),
    Geometry.Curvature.mvfderiv_restrictOpen U F x w (hF.mdifferentiableAt (by simp))]
  rw [SmoothRiemannianMetric.restrictOpen_inner]
  simpa only [F, show (2 : ℝ) ^ 2 = 4 by norm_num, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] using
    hessFun_mul_log_time_sub_inner_scaleMetric 2 (by norm_num) ξ (x : Hyperboloid E) v w

private theorem sq_mvfderiv_two_mul_log_time_sub_inner_restrictOpen_le
    (U : TopologicalSpace.Opens (Hyperboloid E)) (ξ : Metric.sphere (0 : E) 1)
    (x : U) (v : TangentSpace 𝓘(ℝ, E) x) :
    let g := (scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U
    let ρ := fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)
    (mvfderiv 𝓘(ℝ, E) ρ x v) ^ 2 ≤ g.inner x v v := by
  let F := fun y : Hyperboloid E => 2 * Real.log (y.time - inner ℝ (ξ : E) y.space)
  have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ F :=
    contMDiff_const.mul (contMDiff_log_time_sub_inner ξ)
  dsimp only
  rw [Geometry.Curvature.mvfderiv_restrictOpen U F x v (hF.mdifferentiableAt (by simp))]
  rw [SmoothRiemannianMetric.restrictOpen_inner]
  simpa only [F, show (2 : ℝ) ^ 2 = 4 by norm_num] using
    sq_mvfderiv_mul_log_time_sub_inner_le_scaleMetric 2 (by norm_num) ξ (x : Hyperboloid E) v

private theorem hessFun_two_mul_log_time_sub_inner_bounds
    (U : TopologicalSpace.Opens (Hyperboloid E))
    (h : SmoothRiemannianMetric 𝓘(ℝ, E) U) (ξ : Metric.sphere (0 : E) 1)
    {K : Set U} {p : ℕ} (hp : 1 ≤ p)
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U)
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U) ≤ ENNReal.ofReal (1 / 100))
    {x : U} (hx : x ∈ K) (v : TangentSpace 𝓘(ℝ, E) x) (hv : h.inner x v v = 1) :
    let ρ := fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)
    |Geometry.Operator.hessFun h ρ x v v| ≤ 2 / 3 ∧
      (mvfderiv 𝓘(ℝ, E) ρ x v = 0 → 39 / 110 ≤ Geometry.Operator.hessFun h ρ x v v) := by
  let g := (scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U
  let ρ := fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)
  let A := CovariantDerivative.difference
    (Geometry.Connection.LeviCivita h) (Geometry.Connection.LeviCivita g) x v v
  have hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_const.mul (contMDiff_log_time_sub_inner ξ)).comp contMDiff_subtype_val
  have hbounds := quadratic_bounds_of_metricCkENormOn g h hsmall hx v
  rw [hv] at hbounds
  have hGlo : (10 / 11 : ℝ) ≤ g.inner x v v := by linarith only [hbounds.2]
  have hGhi : g.inner x v v ≤ (10 / 9 : ℝ) := by linarith only [hbounds.1]
  have hmodel := hessFun_two_mul_log_time_sub_inner_restrictOpen U ξ x v v
  change Geometry.Operator.hessFun g ρ x v v =
    (1 / 2 : ℝ) * (g.inner x v v - mvfderiv 𝓘(ℝ, E) ρ x v * mvfderiv 𝓘(ℝ, E) ρ x v) at hmodel
  have hcovector := sq_mvfderiv_two_mul_log_time_sub_inner_restrictOpen_le U ξ x v
  change (mvfderiv 𝓘(ℝ, E) ρ x v) ^ 2 ≤ g.inner x v v at hcovector
  have hcovectorA := sq_mvfderiv_two_mul_log_time_sub_inner_restrictOpen_le U ξ x A
  change (mvfderiv 𝓘(ℝ, E) ρ x A) ^ 2 ≤ g.inner x A A at hcovectorA
  have hA := connectionDifference_norm_le_of_metricCkENormOn g h hp hsmall hx v
  change Real.sqrt (g.inner x A A) ≤ (5 / 243 : ℝ) * g.inner x v v at hA
  have hdA : |mvfderiv 𝓘(ℝ, E) ρ x A| ≤ (1 / 10 : ℝ) := by
    have hsqrt : |mvfderiv 𝓘(ℝ, E) ρ x A| ≤ Real.sqrt (g.inner x A A) := by
      rw [← Real.sqrt_sq_eq_abs (mvfderiv 𝓘(ℝ, E) ρ x A)]
      exact Real.sqrt_le_sqrt hcovectorA
    linarith only [hsqrt, hA, hGhi]
  have hdiff := Geometry.Connection.hessFun_sub_eq_neg_mvfderiv_connectionDifference
    h g isOpen_univ hρ.contMDiffOn (Set.mem_univ x) v v
  change Geometry.Operator.hessFun h ρ x v v - Geometry.Operator.hessFun g ρ x v v =
    -mvfderiv 𝓘(ℝ, E) ρ x A at hdiff
  have herr : |Geometry.Operator.hessFun h ρ x v v -
      Geometry.Operator.hessFun g ρ x v v| ≤ (1 / 10 : ℝ) := by
    rw [hdiff, abs_neg]
    exact hdA
  obtain ⟨herrlo, herrhi⟩ := abs_le.mp herr
  dsimp only
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (mvfderiv 𝓘(ℝ, E) ρ x v)]
  · intro hzero
    change mvfderiv 𝓘(ℝ, E) ρ x v = 0 at hzero
    rw [hzero] at hmodel
    nlinarith only [hmodel, herrlo, hGlo]

theorem abs_hessFun_two_mul_log_time_sub_inner_le_of_metricCkENormOn
    (U : TopologicalSpace.Opens (Hyperboloid E))
    (h : SmoothRiemannianMetric 𝓘(ℝ, E) U) (ξ : Metric.sphere (0 : E) 1)
    {K : Set U} {p : ℕ} (hp : 1 ≤ p)
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U)
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U) ≤ ENNReal.ofReal (1 / 100))
    {x : U} (hx : x ∈ K) (v : TangentSpace 𝓘(ℝ, E) x) (hv : h.inner x v v = 1) :
    |Geometry.Operator.hessFun h
      (fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)) x v v| ≤ 2 / 3 :=
  (hessFun_two_mul_log_time_sub_inner_bounds U h ξ hp hsmall hx v hv).1

theorem hessFun_two_mul_log_time_sub_inner_lower_bound_of_metricCkENormOn
    (U : TopologicalSpace.Opens (Hyperboloid E))
    (h : SmoothRiemannianMetric 𝓘(ℝ, E) U) (ξ : Metric.sphere (0 : E) 1)
    {K : Set U} {p : ℕ} (hp : 1 ≤ p)
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U)
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U) ≤ ENNReal.ofReal (1 / 100))
    {x : U} (hx : x ∈ K) (v : TangentSpace 𝓘(ℝ, E) x) (hv : h.inner x v v = 1)
    (hzero : mvfderiv 𝓘(ℝ, E)
      (fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)) x v = 0) :
    (39 / 110 : ℝ) ≤ Geometry.Operator.hessFun h
      (fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)) x v v :=
  (hessFun_two_mul_log_time_sub_inner_bounds U h ξ hp hsmall hx v hv).2 hzero

end DifferentialGeometry.Hyperboloid
