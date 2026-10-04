import DifferentialGeometry.Geometry.Collapse.DistancePerturbationGradient
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Geometry.Comparison.VectorAdaptedStability

/-!
# Integration along minimizing segments inside a buffer (LFR37, Riemannian step)

Blueprint 207A, LFR37 (`lem:collapse-buffered-vector-adapted-stability`, A:28210–28241): "Integrate
`D(J - J(x) - χ)` along minimizing segments. For endpoints in `B(x,100)`, those segments lie in
`B(x,300)`". On a complete Riemannian manifold (the soul-toolkit setting of LC27–LC29):

* `abs_sub_le_of_gradFun_le_on_ball`: if `u` is differentiable on `B(x, 3R)` with
  `‖∇u‖_g ≤ L` there, then `|u(y) - u(z)| ≤ L d(y,z)` for `y, z ∈ B(x, R)` (the minimizing geodesic
  from `y` to `z` stays in `B(x, 3R)`; mean value inequality along it).
* `norm_sub_le_of_gradFun_inner_le_on_ball`: the same for a map `D : M → ℝⁿ` whose every unit
  covector component `⟪e, D⟫` has `‖∇⟪e, D⟫‖_g ≤ L` on `B(x, 3R)` (this is the operator-norm bound
  `‖dD‖ ≤ L` written with gradients), giving `‖D(y) - D(z)‖ ≤ L d(y,z)`; applied to `D = J - χ` this
  is the Lipschitz-difference hypothesis of `vector_adapted_metric_clauses_of_perturbation`.
* `vector_adapted_metric_clauses_riemannian` (LFR37, Lipschitz and image clauses): if `χ` satisfies
  them at quality `γ/4` on `B(x,100)` with `χ(x) = 0`, and `‖d(J - χ)‖_g ≤ γ/100` on `B(x,300)`
  (unit-covector form), then `J` satisfies them at quality `γ` centred at `J(x)`. The derivative
  clause is `norm_sub_lt_of_derivative_perturbation` and rank two is `surjective_of_gram_perturbation`
  applied in the fibre inner product, which is `g_y` by `IsMetricNorm.inner_eq`.
-/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold ENNReal NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator

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

/-- Mean value inequality on `B(x, R)` from a gradient bound on `B(x, 3R)`. -/
theorem abs_sub_le_of_gradFun_le_on_ball (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {u : M → ℝ} {x : M} {R L : ℝ}
    (hu : ∀ y ∈ ball x (3 * R), MDifferentiableAt I 𝓘(ℝ, ℝ) u y)
    (hgrad : ∀ y ∈ ball x (3 * R),
      Real.sqrt (g.inner y (gradFun g u y) (gradFun g u y)) ≤ L)
    {y z : M} (hy : y ∈ ball x R) (hz : z ∈ ball x R) :
    |u y - u z| ≤ L * dist y z := by
  have hfin : riemannianEDist I y z ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨v, hv, hlen⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
    g hEnorm y z hfin
  have hdyz : (riemannianEDist I y z).toReal = dist y z := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rw [hdyz] at hlen
  let γ := intrinsicGeodesic g hEnorm y v
  have hγ0 : γ 0 = y := intrinsicGeodesic_zero g hEnorm y v
  have hγ1 : γ 1 = z := hv
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm y v
  have hyx : dist y x < R := hy
  have hzx : dist z x < R := hz
  have hyz : dist y z < 2 * R := by
    have := dist_triangle y x z
    rw [dist_comm x z] at this
    linarith
  have hin (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ ball x (3 * R) := by
    have h1 : dist (γ 0) (γ t) ≤ Real.sqrt (g.inner y v v) * (t - 0) :=
      dist_intrinsicGeodesic_le_mul g hEnorm y v ht.1
    rw [hγ0, hlen, sub_zero] at h1
    have h2 : dist y z * t ≤ dist y z := mul_le_of_le_one_right dist_nonneg ht.2
    change dist (γ t) x < 3 * R
    have := dist_triangle (γ t) y x
    rw [dist_comm (γ t) y] at this
    linarith
  let f' : ℝ → ℝ := fun t => NormedSpace.fromTangentSpace (u (γ t))
    (mfderiv I 𝓘(ℝ, ℝ) u (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t
      (DifferentialGeometry.Analysis.Calculus.realTangentOne t)))
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s => u (γ s)) (f' t) (Icc 0 1) t :=
    (DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along I u γ t
      (hu (γ t) (hin t ht)) (hγ.contMDiffAt.mdifferentiableAt (by simp))).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖f' t‖ ≤ L * dist y z := by
    let w : TangentSpace I (γ t) := mfderiv 𝓘(ℝ, ℝ) I γ t
      (DifferentialGeometry.Analysis.Calculus.realTangentOne t)
    have hdu : mfderiv I 𝓘(ℝ, ℝ) u (γ t) w = g.inner (γ t) (gradFun g u (γ t)) w :=
      (inner_gradFun g u (γ t) w).symm
    have hcs := abs_inner_le_sqrt_mul_sqrt (I := I) g (γ t) (gradFun g u (γ t)) w
    have hspeed : Real.sqrt (g.inner (γ t) w w) = dist y z := by
      have h := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm y v t
      change g.inner (γ t) w w = g.inner y v v at h
      rw [h, hlen]
    have hg := hgrad (γ t) (hin t (Ico_subset_Icc_self ht))
    calc ‖f' t‖ = |g.inner (γ t) (gradFun g u (γ t)) w| := by
          change ‖NormedSpace.fromTangentSpace (u (γ t)) (mfderiv I 𝓘(ℝ, ℝ) u (γ t) w)‖ = _
          rw [hdu]
          rfl
      _ ≤ Real.sqrt (g.inner (γ t) (gradFun g u (γ t)) (gradFun g u (γ t))) *
          Real.sqrt (g.inner (γ t) w w) := hcs
      _ ≤ L * dist y z := by
          rw [hspeed]
          exact mul_le_mul_of_nonneg_right hg dist_nonneg
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s => u (γ s)) hderiv
    hbound
  simp only [hγ0, hγ1, Real.norm_eq_abs] at hmv
  rw [abs_sub_comm]
  exact hmv

/-- Vector form: a map to `ℝⁿ` whose unit-covector components have gradient norm `≤ L` on
`B(x, 3R)` is `L`-Lipschitz on `B(x, R)`. -/
theorem norm_sub_le_of_gradFun_inner_le_on_ball (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {n : ℕ} [NeZero n] {D : M → EuclideanSpace ℝ (Fin n)} {x : M}
    {R L : ℝ}
    (hD : ∀ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 → ∀ y ∈ ball x (3 * R),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun w => inner ℝ e (D w)) y)
    (hgrad : ∀ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 → ∀ y ∈ ball x (3 * R),
      Real.sqrt (g.inner y (gradFun g (fun w => inner ℝ e (D w)) y)
        (gradFun g (fun w => inner ℝ e (D w)) y)) ≤ L)
    {y z : M} (hy : y ∈ ball x R) (hz : z ∈ ball x R) :
    ‖D y - D z‖ ≤ L * dist y z := by
  by_cases h0 : D y - D z = 0
  · rw [h0, norm_zero]
    have hR : 0 < R := (dist_nonneg (x := y) (y := x)).trans_lt hy
    have hx : x ∈ ball x (3 * R) := mem_ball_self (by linarith)
    have hL : 0 ≤ L := (Real.sqrt_nonneg _).trans
      (hgrad (EuclideanSpace.single 0 1) (by simp) x hx)
    positivity
  · set w := D y - D z with hw
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr h0
    let e : EuclideanSpace ℝ (Fin n) := ‖w‖⁻¹ • w
    have he : ‖e‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hwpos.ne']
    have h := abs_sub_le_of_gradFun_le_on_ball g hEnorm (u := fun v => inner ℝ e (D v))
      (hD e he) (hgrad e he) hy hz
    have hinner : inner ℝ e (D y) - inner ℝ e (D z) = ‖w‖ := by
      rw [← inner_sub_right, ← hw, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [hinner, abs_of_pos hwpos] at h
    exact h

/-- **LFR37 on a complete Riemannian manifold, Lipschitz and image clauses.** -/
theorem vector_adapted_metric_clauses_riemannian (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {x : M} {J χ : M → EuclideanSpace ℝ (Fin 2)} {γ : ℝ}
    (hχx : χ x = 0)
    (hχL : ∀ y ∈ ball x 100, ∀ z ∈ ball x 100, dist (χ y) (χ z) ≤ (1 + γ / 4) * dist y z)
    (hχI : ∀ y ∈ ball x 100, infDist (χ y) (ball (0 : EuclideanSpace ℝ (Fin 2)) 100) ≤
      100 * (γ / 4))
    (hχI' : ∀ w ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100, infDist w (χ '' ball x 100) ≤
      100 * (γ / 4))
    (hD : ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ y ∈ ball x 300,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun w => inner ℝ e (J w - χ w)) y)
    (hgrad : ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 → ∀ y ∈ ball x 300,
      Real.sqrt (g.inner y (gradFun g (fun w => inner ℝ e (J w - χ w)) y)
        (gradFun g (fun w => inner ℝ e (J w - χ w)) y)) ≤ γ / 100) :
    (∀ y ∈ ball x 100, ∀ z ∈ ball x 100, dist (J y) (J z) ≤ (1 + γ) * dist y z) ∧
      (∀ y ∈ ball x 100, infDist (J y) (ball (J x) 100) ≤ 100 * γ) ∧
      ∀ w ∈ ball (J x) 100, infDist w (J '' ball x 100) ≤ 100 * γ := by
  have h300 : (3 : ℝ) * 100 = 300 := by norm_num
  refine DifferentialGeometry.Geometry.Comparison.vector_adapted_metric_clauses_of_perturbation
    hχx hχL hχI hχI' fun y hy z hz => ?_
  exact norm_sub_le_of_gradFun_inner_le_on_ball g hEnorm (D := fun w => J w - χ w) (R := 100)
    (by rw [h300]; exact hD) (by rw [h300]; exact hgrad) hy hz

end DifferentialGeometry.Geometry.Collapse
