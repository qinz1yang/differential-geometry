import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderBackgroundJets
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PullbackTowerBounds

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology

private local instance cylinderErrorC1 (epsilon : ℝ) :
    IsManifold SpatialNeckCylinderModel 1 (spatialNeckBuffer epsilon) :=
  IsManifold.of_le (n := ∞) (by decide)

def cylinderTimeErrorJet (epsilon c : ℝ) (q : ℕ) (_s : ℝ) :
    Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2 :=
  if q = 0 then (c - 1) • metricTensorField (strongNeckBackgroundMetric epsilon 0) else 0

theorem cylinderTimeErrorJet_zero (epsilon c : ℝ) (hc : 0 < c)
    (s : ℝ) (hs : s ≤ 0) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    cylinderTimeErrorJet epsilon c 0 s x v =
      (scaleMetric c hc (strongNeckBackgroundMetric epsilon (s / c))).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1) := by
  rw [strongNeckBackground_scaled_time_error_inner epsilon c hc s hs]
  change (c - 1) * metricTensorField (strongNeckBackgroundMetric epsilon 0) x v = _
  rw [metricTensorField_apply]

theorem cylinderTimeErrorJet_succ (epsilon c s : ℝ) (q : ℕ) :
    cylinderTimeErrorJet epsilon c (q + 1) s = 0 := by
  simp only [cylinderTimeErrorJet, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]

theorem cylinderTimeErrorJet_hasDerivWithinAt (epsilon c : ℝ)
    (q : ℕ) (s : ℝ) (times : Set ℝ) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    HasDerivWithinAt (fun t => cylinderTimeErrorJet epsilon c q t x v)
      (cylinderTimeErrorJet epsilon c (q + 1) s x v) times s := by
  rw [cylinderTimeErrorJet_succ]
  exact hasDerivWithinAt_const s times (cylinderTimeErrorJet epsilon c q s x v)

theorem cylinderTimeErrorJet_spatial_succ (epsilon c s : ℝ) (q a : ℕ) :
    tensor02CovDeriv (cylinderTimeErrorJet epsilon c q s)
      (strongNeckBackgroundMetric epsilon s) (a + 1) = 0 := by
  by_cases hq : q = 0
  · rw [cylinderTimeErrorJet, ite_eq_left hq,
      tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_smul,
      ← tensor02_cov_deriv_eq_cov_deriv_of_field,
      strongNeckBackground_metric_tensor_parallel, smul_zero]
  · rw [cylinderTimeErrorJet, ite_eq_right hq,
      tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]

theorem cylinderTimeErrorJet_covNorm_le (epsilon c s : ℝ)
    (hs : s ∈ Icc (-1 : ℝ) 0) (q a : ℕ) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a (cylinderTimeErrorJet epsilon c q s)
        (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x ≤
      |c - 1| * (3 * Real.sqrt 3) := by
  cases a with
  | zero =>
    by_cases hq : q = 0
    · have hpoint := (shrinkingCylinder_backward_forward_reference_equivalent
        1 s (by norm_num) hs).2 (x : SpatialNeckCylinder) (mem_univ _)
      have hpair : ∀ v : TangentSpace SpatialNeckCylinderModel x,
          (3 : ℝ)⁻¹ * (strongNeckBackgroundMetric epsilon 0).inner x v v ≤
            (strongNeckBackgroundMetric epsilon s).inner x v v ∧
          (strongNeckBackgroundMetric epsilon s).inner x v v ≤
            3 * (strongNeckBackgroundMetric epsilon 0).inner x v v := by
        intro v
        simpa only [sub_self, strongNeckBackgroundMetric_of_nonpos epsilon 0 le_rfl,
          strongNeckBackgroundMetric_of_nonpos epsilon s hs.2,
          SmoothRiemannianMetric.restrictOpen_inner] using hpoint v
      have hn := covNorm0_le (strongNeckBackgroundMetric epsilon 0)
        (strongNeckBackgroundMetric epsilon s) x (C := 3) (by norm_num) hpair
      have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
      rw [hdim] at hn
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric epsilon s) x 2
        (metricTensorField (strongNeckBackgroundMetric epsilon 0) x)) ≤ 3 * Real.sqrt 3 at hn
      rw [cylinderTimeErrorJet, ite_eq_left hq]
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric epsilon s) x 2
        ((c - 1) • metricTensorField (strongNeckBackgroundMetric epsilon 0) x)) ≤ _
      rw [sqrt_normSq0S_smul]
      exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)
    · rw [cylinderTimeErrorJet, ite_eq_right hq, tensor02CovDerivNormWith,
        tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero]
      positivity
  | succ a =>
    rw [tensor02CovDerivNormWith, cylinderTimeErrorJet_spatial_succ]
    simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
      MetricFiberData.inner, map_zero, Real.sqrt_zero]
    positivity

section ReferencePerturbation

theorem strongNeckBackground_covNorm_le_zero
    (ε v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 0)
    (A : Tensor0SField (I := SpatialNeckCylinderModel) (M := spatialNeckBuffer ε) ∞ 2)
    (r : ℕ) (x : spatialNeckBuffer ε) :
    tensor02CovDerivNormWith r A (strongNeckBackgroundMetric ε v)
      (strongNeckBackgroundMetric ε v) x ≤
      Real.sqrt ((3 : ℝ) ^ (r + 2)) * tensor02CovDerivNormWith r A
        (strongNeckBackgroundMetric ε 0) (strongNeckBackgroundMetric ε 0) x := by
  simpa only [sub_self] using strongNeckBackground_backward_forward_covNorm_le ε 1 v
    (by norm_num) hv A r x

theorem strongNeckBackground_metric_tensor_parallel_at
    (ε u v : ℝ) (r : ℕ) :
    tensor02CovDeriv (metricTensorField (strongNeckBackgroundMetric ε u))
      (strongNeckBackgroundMetric ε v) (r + 1) = 0 := by
  rw [strongNeckBackground_tensor02CovDeriv_eq ε v u,
    tensor02_cov_deriv_eq_cov_deriv_of_field, ← metricCovDeriv_eq_covDerivOfField]
  exact covDeriv_self_succ _ r

theorem strongNeckBackground_time_difference_tensor
    (ε u v : ℝ) (hu : u ≤ 0) (hv : v ≤ 0) :
    metricTensorField (strongNeckBackgroundMetric ε u) -
      metricTensorField (strongNeckBackgroundMetric ε v) =
    (v - u) • (metricTensorField (strongNeckBackgroundMetric ε (-1)) -
      metricTensorField (strongNeckBackgroundMetric ε 0)) := by
  ext x w
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
    metricTensorField_apply]
  rw [strongNeckBackgroundMetric_of_nonpos ε u hu,
    strongNeckBackgroundMetric_of_nonpos ε v hv,
    strongNeckBackgroundMetric_of_nonpos ε (-1) (by norm_num),
    strongNeckBackgroundMetric_of_nonpos ε 0 le_rfl]
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  have h (t : ℝ) (ht : t < 1) := scalarOneShrinkingCylinderMetric_inner t ht x.1.1 x.1.2
    (w 0).1 (w 1).1 (w 0).2 (w 1).2
  have heq (t : ℝ) (ht : t < 1) :
      (scalarOneShrinkingCylinderMetric t ht).inner x.1 (w 0) (w 1) =
        2 * (1 - t) * (Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
          x.1.1 (w 0).1 (w 1).1 + (w 0).2 * (w 1).2 := h t ht
  change (scalarOneShrinkingCylinderMetric u _).inner x.1 (w 0) (w 1) -
    (scalarOneShrinkingCylinderMetric v _).inner x.1 (w 0) (w 1) = _
  simp only [heq]
  ring

theorem strongNeckBackground_time_difference_covNorm_le
    (ε u v : ℝ) (hu : u ∈ Icc (-1 : ℝ) 0) (hv : v ∈ Icc (-1 : ℝ) 0)
    (r : ℕ) (x : spatialNeckBuffer ε) :
    tensor02CovDerivNormWith r
      (metricTensorField (strongNeckBackgroundMetric ε u) -
        metricTensorField (strongNeckBackgroundMetric ε v))
      (strongNeckBackgroundMetric ε v) (strongNeckBackgroundMetric ε v) x ≤
      |u - v| * (6 * Real.sqrt 3) := by
  cases r with
  | zero =>
    rw [strongNeckBackground_time_difference_tensor ε u v hu.2 hv.2,
      tensor02CovDerivNormWith_smul, abs_sub_comm v u]
    have hmetric (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 0) :
        tensor02CovDerivNormWith 0 (metricTensorField (strongNeckBackgroundMetric ε t))
          (strongNeckBackgroundMetric ε v) (strongNeckBackgroundMetric ε v) x ≤
          3 * Real.sqrt 3 := by
      have h := (shrinkingCylinder_backward_forward_reference_equivalent (1 - t) v
        (by constructor <;> linarith [ht.1, ht.2]) hv).2 x.1 (mem_univ _)
      have heq : ∀ V : TangentSpace SpatialNeckCylinderModel x,
          (3 : ℝ)⁻¹ * (strongNeckBackgroundMetric ε t).inner x V V ≤
              (strongNeckBackgroundMetric ε v).inner x V V ∧
            (strongNeckBackgroundMetric ε v).inner x V V ≤
              3 * (strongNeckBackgroundMetric ε t).inner x V V := by
        intro V
        simpa only [sub_sub_cancel, strongNeckBackgroundMetric_of_nonpos ε t ht.2,
          strongNeckBackgroundMetric_of_nonpos ε v hv.2,
          SmoothRiemannianMetric.restrictOpen_inner] using h V
      have hb := covNorm0_le (strongNeckBackgroundMetric ε t)
        (strongNeckBackgroundMetric ε v) x (by norm_num : (1 : ℝ) ≤ 3) heq
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric ε v) x 2
        (metricTensorField (strongNeckBackgroundMetric ε t) x)) ≤ 3 * Real.sqrt 3
      simpa only [metricCovDerivNorm, metricCovDeriv, Nat.rec_zero,
        show Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 by simp,
        Nat.cast_ofNat] using hb
    have hn0 := hmetric 0 (by norm_num)
    have hn1 := hmetric (-1) (by norm_num)
    have hsub : tensor02CovDerivNormWith 0
        (metricTensorField (strongNeckBackgroundMetric ε (-1)) -
          metricTensorField (strongNeckBackgroundMetric ε 0))
        (strongNeckBackgroundMetric ε v) (strongNeckBackgroundMetric ε v) x ≤
          6 * Real.sqrt 3 := by
      have htri := _root_.DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_add_le
        (strongNeckBackgroundMetric ε v) x 2
        (metricTensorField (strongNeckBackgroundMetric ε (-1)) x)
        (-metricTensorField (strongNeckBackgroundMetric ε 0) x)
      simp only [_root_.DifferentialGeometry.Tensor0SBundle.normSq0S_neg] at htri
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric ε v) x 2
        (metricTensorField (strongNeckBackgroundMetric ε (-1)) x -
          metricTensorField (strongNeckBackgroundMetric ε 0) x)) ≤ _
      rw [sub_eq_add_neg]
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric ε v) x 2
        (metricTensorField (strongNeckBackgroundMetric ε 0) x)) ≤ 3 * Real.sqrt 3 at hn0
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric ε v) x 2
        (metricTensorField (strongNeckBackgroundMetric ε (-1)) x)) ≤ 3 * Real.sqrt 3 at hn1
      exact htri.trans (by linarith)
    exact mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
  | succ r =>
    rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
      covDerivOfField_sub, ← tensor02_cov_deriv_eq_cov_deriv_of_field,
      ← tensor02_cov_deriv_eq_cov_deriv_of_field,
      strongNeckBackground_metric_tensor_parallel_at,
      strongNeckBackground_metric_tensor_parallel_at, sub_self]
    simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
      MetricFiberData.inner, map_zero, Real.sqrt_zero]
    positivity

theorem strongNeckBackground_metric_tensor_covNorm_le
    (ε u v : ℝ) (hu : u ∈ Icc (-1 : ℝ) 0) (hv : v ∈ Icc (-1 : ℝ) 0)
    (r : ℕ) (x : spatialNeckBuffer ε) :
    tensor02CovDerivNormWith r (metricTensorField (strongNeckBackgroundMetric ε u))
      (strongNeckBackgroundMetric ε v) (strongNeckBackgroundMetric ε v) x ≤
        3 * Real.sqrt 3 := by
  cases r with
  | zero =>
    have h := (shrinkingCylinder_backward_forward_reference_equivalent (1 - u) v
      (by constructor <;> linarith [hu.1, hu.2]) hv).2 x.1 (mem_univ _)
    have heq : ∀ V : TangentSpace SpatialNeckCylinderModel x,
        (3 : ℝ)⁻¹ * (strongNeckBackgroundMetric ε u).inner x V V ≤
            (strongNeckBackgroundMetric ε v).inner x V V ∧
          (strongNeckBackgroundMetric ε v).inner x V V ≤
            3 * (strongNeckBackgroundMetric ε u).inner x V V := by
      intro V
      simpa only [sub_sub_cancel, strongNeckBackgroundMetric_of_nonpos ε u hu.2,
        strongNeckBackgroundMetric_of_nonpos ε v hv.2,
        SmoothRiemannianMetric.restrictOpen_inner] using h V
    have hb := covNorm0_le (strongNeckBackgroundMetric ε u)
      (strongNeckBackgroundMetric ε v) x (by norm_num : (1 : ℝ) ≤ 3) heq
    change Real.sqrt (normSq0S (strongNeckBackgroundMetric ε v) x 2
      (metricTensorField (strongNeckBackgroundMetric ε u) x)) ≤ 3 * Real.sqrt 3
    simpa only [metricCovDerivNorm, metricCovDeriv, Nat.rec_zero,
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 by simp,
      Nat.cast_ofNat] using hb
  | succ r =>
    rw [tensor02CovDerivNormWith, strongNeckBackground_metric_tensor_parallel_at]
    simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
      MetricFiberData.inner, map_zero, Real.sqrt_zero]
    positivity

theorem strongNeckBackground_scale_time_error_covNorm_le
    (ε c u v : ℝ) (hc : 0 < c) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-1 : ℝ) 0) (r : ℕ) (x : spatialNeckBuffer ε) :
    tensor02CovDerivNormWith r
      (metricTensorField (scaleMetric c hc (strongNeckBackgroundMetric ε u)) -
        metricTensorField (strongNeckBackgroundMetric ε v))
      (strongNeckBackgroundMetric ε v) (strongNeckBackgroundMetric ε v) x ≤
      (|c - 1| + 2 * |u - v|) * (3 * Real.sqrt 3) := by
  let gV := strongNeckBackgroundMetric ε v
  let A := metricTensorField (strongNeckBackgroundMetric ε u)
  let B := metricTensorField gV
  have heq : metricTensorField (scaleMetric c hc (strongNeckBackgroundMetric ε u)) - B =
      (c - 1) • A + (A - B) := by
    ext y w
    simp only [metricTensorField_apply, scaleMetric_inner, ContMDiffSection.coe_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, Tensor0SSpace.sub_apply, Tensor0SSpace.add_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul]
    dsimp [A, B, gV]
    simp only [metricTensorField_apply]
    ring
  have htri : tensor02CovDerivNormWith r ((c - 1) • A + (A - B)) gV gV x ≤
      tensor02CovDerivNormWith r ((c - 1) • A) gV gV x +
        tensor02CovDerivNormWith r (A - B) gV gV x := by
    simp only [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
      covDerivOfField_add, ContMDiffSection.coe_add, Pi.add_apply]
    exact _root_.DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_add_le gV x (r + 2) _ _
  rw [heq]
  have hfirst : tensor02CovDerivNormWith r ((c - 1) • A) gV gV x ≤
      |c - 1| * (3 * Real.sqrt 3) := by
    rw [tensor02CovDerivNormWith_smul]
    exact mul_le_mul_of_nonneg_left
      (strongNeckBackground_metric_tensor_covNorm_le ε u v hu hv r x) (abs_nonneg _)
  have hsecond := strongNeckBackground_time_difference_covNorm_le ε u v hu hv r x
  exact htri.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

def shrinkingCylinderTimeJet (ε : ℝ) (b : ℕ) (v : ℝ) :
    Tensor0SField (I := SpatialNeckCylinderModel) (M := spatialNeckBuffer ε) ∞ 2 :=
  if b = 0 then metricTensorField (strongNeckBackgroundMetric ε v)
  else if b = 1 then metricTensorField (strongNeckBackgroundMetric ε 0) -
    metricTensorField (strongNeckBackgroundMetric ε (-1)) else 0

theorem shrinkingCylinderTimeJet_hasDerivWithinAt (ε : ℝ) (b : ℕ)
    {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 0) (x : spatialNeckBuffer ε) :
    ∀ w : Fin 2 → TangentSpace SpatialNeckCylinderModel x,
      HasDerivWithinAt (fun u => shrinkingCylinderTimeJet ε b u x w)
        (shrinkingCylinderTimeJet ε (b + 1) v x w) (Icc (-1 : ℝ) 0) v := by
  intro w
  by_cases hb0 : b = 0
  · subst b
    let A := metricTensorField (strongNeckBackgroundMetric ε 0) x w
    let B := metricTensorField (strongNeckBackgroundMetric ε (-1)) x w
    have hd : HasDerivAt (fun u : ℝ => A + u • (A - B)) (A - B) v := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id v).smul_const (A - B)).const_add A
    have heq (u : ℝ) (hu : u ≤ 0) :
        metricTensorField (strongNeckBackgroundMetric ε u) x w = A + u • (A - B) := by
      have hh := congrArg (fun T : Tensor0SField (I := SpatialNeckCylinderModel)
        (M := spatialNeckBuffer ε) ∞ 2 => T x w)
          (strongNeckBackground_time_difference_tensor ε u 0 hu le_rfl)
      change metricTensorField (strongNeckBackgroundMetric ε u) x w - A =
        (0 - u) • (B - A) at hh
      have hmul : (0 - u) • (B - A) = u • (A - B) := by module
      rw [hmul] at hh
      exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)
    have hpoint : shrinkingCylinderTimeJet ε 0 v x w = A + v • (A - B) := by
      simp only [shrinkingCylinderTimeJet]
      exact heq v hv.2
    have hfun : ∀ᶠ u in 𝓝[Icc (-1 : ℝ) 0] v,
        shrinkingCylinderTimeJet ε 0 u x w = A + u • (A - B) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact heq u hu.2
    have hnext : shrinkingCylinderTimeJet ε (0 + 1) v x w = A - B := by
      simp only [shrinkingCylinderTimeJet, Nat.zero_add, one_ne_zero, ite_false, ite_true]
      rfl
    rw [hnext]
    exact hd.hasDerivWithinAt.congr_of_eventuallyEq hfun hpoint
  · have hnext : shrinkingCylinderTimeJet ε (b + 1) v = 0 := by
      simp only [shrinkingCylinderTimeJet, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ite_false]
      rw [ite_eq_right (by omega)]
    rw [hnext]
    change HasDerivWithinAt _ (0 : ℝ) (Icc (-1 : ℝ) 0) v
    by_cases hb1 : b = 1
    · simpa only [shrinkingCylinderTimeJet, hb1, one_ne_zero, ite_false, ite_true,
        ContMDiffSection.coe_zero,
        Pi.zero_apply, zero_apply] using
        hasDerivWithinAt_const v (Icc (-1 : ℝ) 0)
          ((metricTensorField (strongNeckBackgroundMetric ε 0) -
            metricTensorField (strongNeckBackgroundMetric ε (-1))) x w)
    · simpa only [shrinkingCylinderTimeJet, ite_eq_right hb0, ite_eq_right hb1, ContMDiffSection.coe_zero,
        Pi.zero_apply, zero_apply] using
        hasDerivWithinAt_const v (Icc (-1 : ℝ) 0)
          (0 : ℝ)

theorem shrinkingCylinderTimeJet_scale_time_error_covNorm_le
    (ε c u v : ℝ) (hc : 0 < c) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-1 : ℝ) 0) (b r : ℕ) (x : spatialNeckBuffer ε) :
    tensor02CovDerivNormWith r
      ((c * c⁻¹ ^ b) • shrinkingCylinderTimeJet ε b u - shrinkingCylinderTimeJet ε b v)
      (strongNeckBackgroundMetric ε v) (strongNeckBackgroundMetric ε v) x ≤
      (|c - 1| + 2 * |u - v|) * (3 * Real.sqrt 3) := by
  by_cases hb0 : b = 0
  · subst b
    have heq : (c * c⁻¹ ^ 0) • shrinkingCylinderTimeJet ε 0 u =
        metricTensorField (scaleMetric c hc (strongNeckBackgroundMetric ε u)) := by
      ext y w
      simp only [shrinkingCylinderTimeJet, ite_true, pow_zero, mul_one,
        ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
        metricTensorField_apply, scaleMetric_inner]
    rw [heq]
    exact strongNeckBackground_scale_time_error_covNorm_le ε c u v hc hu hv r x
  · have heq : (c * c⁻¹ ^ b) • shrinkingCylinderTimeJet ε b u -
        shrinkingCylinderTimeJet ε b v = 0 := by
      by_cases hb1 : b = 1
      · subst b
        simp only [shrinkingCylinderTimeJet, one_ne_zero, ite_false, ite_true,
          pow_one, mul_inv_cancel₀ hc.ne', one_smul, sub_self]
      · simp only [shrinkingCylinderTimeJet, ite_eq_right hb0, ite_eq_right hb1, smul_zero, sub_self]
    rw [heq, tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
      covDerivOfField_zero_tensor]
    simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
      MetricFiberData.inner, map_zero, Real.sqrt_zero]
    positivity

end ReferencePerturbation

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
