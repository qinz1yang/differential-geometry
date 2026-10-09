import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformTipCurvature
import DifferentialGeometry.Geometry.Curvature.RicciUniformPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Unweighted
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ParabolicScaling
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricReference
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance (U : TopologicalSpace.Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

private theorem exists_uniform_standard_metric_two_jet_reference_bound
    (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens E3),
      ∀ t ∈ Icc 0 T, ∀ (G : SmoothRiemannianMetric (𝓡 3) U) (x : U) (q : ℕ), q ≤ 2 →
        metricDerivNorm q G ((Q.val.metric t).restrictOpen U)
          ((Q.val.metric t).restrictOpen U) x ≤
          D * ∑ j ∈ Finset.range 3, metricDerivNorm j G ((Q.val.metric t).restrictOpen U)
            (StandardCap.metric.restrictOpen U) x := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_standard_metric_deriv_norm_reference_bound T hT hT1 2
  refine ⟨D, hD, ?_⟩
  intro Q U t ht G x q hq
  exact hbound U Q t ht G ((Q.val.metric t).restrictOpen U) q hq x

theorem exists_uniform_standard_metric_scalar_lower_comparison
    (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens E3)
      (G : SmoothRiemannianMetric (𝓡 3) U), ∀ t ∈ Icc 0 T, ∀ x : U,
      (∀ j : ℕ, j ≤ 2 → metricDerivNorm j G ((Q.val.metric t).restrictOpen U)
        (StandardCap.metric.restrictOpen U) x ≤ eta) →
      (∀ v : TangentSpace (𝓡 3) x,
        (1 / 2) * ((Q.val.metric t).restrictOpen U).inner x v v ≤ G.inner x v v) ∧
      (1 / 2) * metricScalarAt ((Q.val.metric t).restrictOpen U) x ≤ metricScalarAt G x := by
  have hTl : ENNReal.ofReal T < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hT1
  obtain ⟨_, K, hK, hRm⟩ := uniformStandardLifetime_slab T hT hTl
  obtain ⟨D, hD, hreference⟩ := exists_uniform_standard_metric_two_jet_reference_bound T hT hT1
  obtain ⟨c, hc, hscalar⟩ := exists_standard_scalar_lower_bound
  let B := 9 * (864 + 18 * K)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let delta := min (1 / 6) (c / (2 * (B + 1)))
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  have hd6 : delta ≤ 1 / 6 := min_le_left _ _
  have hdB : B * delta ≤ c / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp
      (min_le_right (1 / 6) (c / (2 * (B + 1))))
    change delta * (2 * (B + 1)) ≤ c at hh
    nlinarith
  let eta := delta / (3 * (D + 1))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hDeta : D * (3 * eta) ≤ delta := by
    have hid : eta * (3 * (D + 1)) = delta := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨eta, heta, ?_⟩
  intro Q U G t ht x hjets
  let g := (Q.val.metric t).restrictOpen U
  have hjet : ∀ j : ℕ, j ≤ 2 → metricDerivNorm j G g g x ≤ delta := by
    intro j hj
    have hsum : (∑ k ∈ Finset.range 3, metricDerivNorm k G g
        (StandardCap.metric.restrictOpen U) x) ≤ 3 * eta := by
      calc
        _ ≤ ∑ _k ∈ Finset.range 3, eta := Finset.sum_le_sum fun k hk =>
          hjets k (by have := Finset.mem_range.mp hk; omega)
        _ = 3 * eta := by simp
    exact (hreference Q U t ht G x j hj).trans
      ((mul_le_mul_of_nonneg_left hsum hD).trans hDeta)
  have hric : ∀ v : TangentSpace (𝓡 3) x,
      |ricciTensor g x v v| ≤ (9 * K) * g.inner x v v := by
    intro v
    have hh := ricci_quadratic_form_bound_of_solution_curvature_bound
      Q.val.toSolutionOn x.val v (Real.sqrt_le_iff.mp (hRm Q t ht x.val)).2
    simpa only [g, DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen,
      SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply,
      PartialStandardSolution.toSolutionOn_metric, finrank_euclideanSpace, Fintype.card_fin,
      Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num, Real.sqrt_sq hK] using hh
  have hdiff := Perelman.KappaSolutions.metricScalar_difference_le_relative_two_jets g G x hdelta.le
    (by linarith : delta ≤ 1) (by simpa using (show (3 : ℝ) * delta ≤ 1 / 2 by linarith))
    hjet hric
  have hdiff' : |metricScalarAt G x - metricScalarAt g x| ≤ B * delta := by
    simpa only [B, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      show (3 : ℝ) ^ 2 = 9 by norm_num, show (2 : ℝ) * (9 * K) = 18 * K by ring] using hdiff
  have hsc : c ≤ metricScalarAt g x := by
    have ht1 : t < 1 := ht.2.trans_lt hT1
    have hcle : c ≤ c / (1 - t) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 - t)).mpr
      nlinarith [mul_nonneg hc.le ht.1]
    exact hcle.trans (by
      simpa only [g, metricScalarAt_restrictOpen] using hscalar Q x.val t ⟨ht.1, ht1⟩)
  constructor
  · intro v
    have hb := DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le
      g G x (hjet 0 (by norm_num)) v
    have hn := metric_inner_self_nonneg g x v
    have hsmall := mul_le_mul_of_nonneg_right (by linarith : delta ≤ 1 / 2) hn
    linarith [hb.1]
  · have hlow := (abs_le.mp hdiff').1
    nlinarith

theorem exists_uniform_standard_metric_scalar_upper_comparison
    (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ eta C L : ℝ, 0 < eta ∧ 0 < C ∧ 0 < L ∧
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (G : SmoothRiemannianMetric (𝓡 3) U), ∀ t ∈ Icc 0 T, ∀ x : U,
        (∀ j : ℕ, j ≤ 2 → metricDerivNorm j G ((Q.val.metric t).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ eta) →
        metricScalarAt G x ≤ C ∧ ∀ v : TangentSpace (𝓡 3) x,
          G.inner x v v ≤ L ^ 2 * (StandardCap.metric.restrictOpen U).inner x v v := by
  have hTl : ENNReal.ofReal T < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hT1
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab T hT hTl
  obtain ⟨Λ, hΛ, A, F, hA, hF, hmetric⟩ :=
    standard_metric_bounds_on_shorter_windows T K hT hK
  obtain ⟨D, hD, hreference⟩ :=
    exists_uniform_standard_metric_two_jet_reference_bound T hT hT1
  let eta := (1 / 6 : ℝ) / (3 * (D + 1))
  let B := 9 * (864 + 18 * K)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hDeta : D * (3 * eta) ≤ 1 / 6 := by
    have hid : eta * (3 * (D + 1)) = 1 / 6 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨eta, 9 * K + B / 6 + 1, 2 * Λ, heta, by positivity, by linarith, ?_⟩
  intro Q U G t ht x hjets
  let g := (Q.val.metric t).restrictOpen U
  have hjet : ∀ j : ℕ, j ≤ 2 → metricDerivNorm j G g g x ≤ 1 / 6 := by
    intro j hj
    have hsum : (∑ k ∈ Finset.range 3, metricDerivNorm k G g
        (StandardCap.metric.restrictOpen U) x) ≤ 3 * eta := by
      calc
        _ ≤ ∑ _k ∈ Finset.range 3, eta := Finset.sum_le_sum fun k hk =>
          hjets k (by have := Finset.mem_range.mp hk; omega)
        _ = 3 * eta := by simp
    exact (hreference Q U t ht G x j hj).trans
      ((mul_le_mul_of_nonneg_left hsum hD).trans hDeta)
  have hric : ∀ v : TangentSpace (𝓡 3) x,
      |ricciTensor g x v v| ≤ (9 * K) * g.inner x v v := by
    intro v
    have hh := ricci_quadratic_form_bound_of_solution_curvature_bound
      Q.val.toSolutionOn x.val v (Real.sqrt_le_iff.mp (hRm Q t ht x.val)).2
    simpa only [g, DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen,
      SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply,
      PartialStandardSolution.toSolutionOn_metric, finrank_euclideanSpace, Fintype.card_fin,
      Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num, Real.sqrt_sq hK] using hh
  have hdiff := Perelman.KappaSolutions.metricScalar_difference_le_relative_two_jets g G x
    (by norm_num : (0 : ℝ) ≤ 1 / 6) (by norm_num : (1 / 6 : ℝ) ≤ 1)
    (by norm_num) hjet hric
  have hdiff' : |metricScalarAt G x - metricScalarAt g x| ≤ B / 6 := by
    simpa only [B, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      show (3 : ℝ) ^ 2 = 9 by norm_num, show (2 : ℝ) * (9 * K) = 18 * K by ring,
      mul_one_div] using hdiff
  have hsc : metricScalarAt g x ≤ 9 * K := by
    rw [metricScalarAt_restrictOpen]
    have hh := scalar_abs_le_rm (Q.val.metric t) x.val
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x.val) = 3 :=
      finrank_euclideanSpace_fin
    have hb : |metricScalarAt (Q.val.metric t) x.val| ≤
        9 * Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S (Q.val.metric t)
          x.val 4 (metricRm04 (Q.val.metric t) x.val)) := by
      simpa only [metricRm04_apply, hdim,
        Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
    exact (le_abs_self _).trans (hb.trans
      (mul_le_mul_of_nonneg_left (hRm Q t ht x.val) (by norm_num)))
  constructor
  · linarith [(abs_le.mp hdiff').2]
  · intro v
    have hg := ((hmetric Q.val T hT le_rfl (hlife Q) (hRm Q)).1 t ht).2
      x.val (mem_univ _) v
    have hg' : g.inner x v v ≤ Λ * (StandardCap.metric.restrictOpen U).inner x v v := by
      simpa only [g, SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply] using hg.2
    have hb := (DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le
      g G x (hjet 0 (by norm_num)) v).2
    have hcoef : (1 + (1 / 6 : ℝ)) * Λ ≤ (2 * Λ) ^ 2 := by nlinarith
    calc
      G.inner x v v ≤ (1 + (1 / 6 : ℝ)) * g.inner x v v := hb
      _ ≤ (1 + (1 / 6 : ℝ)) *
          (Λ * (StandardCap.metric.restrictOpen U).inner x v v) :=
        mul_le_mul_of_nonneg_left hg' (by norm_num)
      _ ≤ (2 * Λ) ^ 2 * (StandardCap.metric.restrictOpen U).inner x v v := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcoef
          (metric_inner_self_nonneg (StandardCap.metric.restrictOpen U) x v)


theorem exists_unweighted_action_lower_bound_of_standard_metric_approximation
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) U) (alpha : ℝ → U) (tau : ℝ),
        0 < tau → tau ≤ theta → ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 alpha (Icc 0 tau) →
        (∀ t ∈ Icc 0 tau, ∀ j : ℕ, j ≤ 2 →
          metricDerivNorm j (g t) ((Q.val.metric t).restrictOpen U)
            (StandardCap.metric.restrictOpen U) (alpha t) ≤ eta) →
        (tau = theta ∨
          ENNReal.ofReal r ≤ riemannianEDistOf StandardCap.metric (alpha 0).val (alpha tau).val) →
        ENNReal.ofReal Lambda <
          ∫⁻ t in Ioc (0 : ℝ) tau, ENNReal.ofReal
            (metricScalarAt (g t) (alpha t) +
              (g t).inner (alpha t) (lVelocity alpha t) (lVelocity alpha t)) := by
  obtain ⟨theta,r,htheta,hr,hmodel⟩ :=
    exists_standard_unweighted_action_lower_bound (2 * Lambda) (by positivity)
  obtain ⟨eta,heta,hcompare⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison theta htheta.1.le htheta.2
  refine ⟨theta,r,eta,htheta,hr,heta,?_⟩
  intro Q U g alpha tau htau htautheta halpha hclose halt
  have hsubtype : ContMDiff (𝓡 3) (𝓡 3) 1 (Subtype.val : U → EuclideanSpace ℝ (Fin 3)) :=
    contMDiff_subtype_val
  have hglobal : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1
      (fun t => (alpha t).val) (Icc 0 tau) := hsubtype.comp_contMDiffOn halpha
  have hlarge := hmodel Q (fun t => (alpha t).val) tau htau htautheta hglobal halt
  rw [← unweighted_action_restrictOpen Q.val.metric U alpha 0 tau halpha] at hlarge
  have hhalf : (ENNReal.ofReal (1 / 2 : ℝ)) * ENNReal.ofReal (2 * Lambda) =
      ENNReal.ofReal Lambda := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  have hstrict : ENNReal.ofReal Lambda < (ENNReal.ofReal (1 / 2 : ℝ)) *
      ∫⁻ t in Ioc (0 : ℝ) tau, ENNReal.ofReal
        (metricScalarAt ((Q.val.metric t).restrictOpen U) (alpha t) +
          ((Q.val.metric t).restrictOpen U).inner (alpha t) (lVelocity alpha t) (lVelocity alpha t)) := by
    rw [← hhalf]
    exact ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top hlarge
  apply hstrict.trans_le
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioc
  intro t ht
  obtain ⟨hmetric,hscalar⟩ := hcompare Q U (g t) t ⟨ht.1.le,ht.2.trans htautheta⟩
    (alpha t) (hclose t ⟨ht.1.le,ht.2⟩)
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply ENNReal.ofReal_le_ofReal
  have hspeed := hmetric (lVelocity alpha t)
  linarith

private theorem standard_endpoint_separation_of_ball_exit {r : ℝ} (hr : 0 ≤ r)
    (x y : E3)
    (hstart : riemannianEDistOf StandardCap.metric 0 x ≤ ENNReal.ofReal r)
    (hfar : ENNReal.ofReal (2 * r) ≤ riemannianEDistOf StandardCap.metric 0 y) :
    ENNReal.ofReal r ≤ riemannianEDistOf StandardCap.metric x y := by
  have hx : ‖x‖ ≤ r := (ENNReal.ofReal_le_ofReal_iff hr).mp
    (by simpa only [StandardCap.edist_zero] using hstart)
  have hy : 2 * r ≤ ‖y‖ := (ENNReal.ofReal_le_ofReal_iff (norm_nonneg y)).mp
    (by simpa only [StandardCap.edist_zero] using hfar)
  have hgap : r ≤ |‖y‖ - ‖x‖| := (by linarith : r ≤ ‖y‖ - ‖x‖).trans (le_abs_self _)
  exact (ENNReal.ofReal_le_ofReal hgap).trans (StandardCap.radial_difference_le_edist x y)

theorem exists_unweighted_action_lower_bound_of_standard_metric_approximation_of_ball_exit
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) U) (alpha : ℝ → U) (tau : ℝ),
        0 < tau → tau ≤ theta → ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 alpha (Icc 0 tau) →
        (∀ t ∈ Icc 0 tau, ∀ j : ℕ, j ≤ 2 →
          metricDerivNorm j (g t) ((Q.val.metric t).restrictOpen U)
            (StandardCap.metric.restrictOpen U) (alpha t) ≤ eta) →
        riemannianEDistOf StandardCap.metric 0 (alpha 0).val ≤ ENNReal.ofReal r →
        (tau = theta ∨
          ENNReal.ofReal (2 * r) ≤ riemannianEDistOf StandardCap.metric 0 (alpha tau).val) →
        ENNReal.ofReal Lambda <
          ∫⁻ t in Ioc (0 : ℝ) tau, ENNReal.ofReal
            (metricScalarAt (g t) (alpha t) +
              (g t).inner (alpha t) (lVelocity alpha t) (lVelocity alpha t)) := by
  obtain ⟨theta, r, eta, htheta, hr, heta, hb⟩ :=
    exists_unweighted_action_lower_bound_of_standard_metric_approximation Lambda hLambda
  refine ⟨theta, r, eta, htheta, hr, heta, ?_⟩
  intro Q U g alpha tau htau htautheta halpha hclose hstart halt
  apply hb Q U g alpha tau htau htautheta halpha hclose
  exact halt.imp id (fun hfar => standard_endpoint_separation_of_ball_exit hr.le
    (alpha 0).val (alpha tau).val hstart hfar)


universe u

theorem exists_unweighted_action_lower_bound_of_rescaled_standard_metric_approximation
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N],
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (Ξ : U → N)
        (hΞ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Ξ)
        (alpha : ℝ → U) (b s q : ℝ) (hq : 0 < q),
        b < s → q * (s - b) ≤ theta →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 alpha (Icc b s) →
        (∀ t ∈ Icc 0 (q * (s - b)), ∀ j : ℕ, j ≤ 2 →
          metricDerivNorm j (localPullMetric (scaleMetric q hq (g (b + t / q))) Ξ hΞ)
            ((Q.val.metric t).restrictOpen U) (StandardCap.metric.restrictOpen U)
            (alpha (b + t / q)) ≤ eta) →
        (q * (s - b) = theta ∨
          ENNReal.ofReal r ≤ riemannianEDistOf StandardCap.metric (alpha b).val (alpha s).val) →
        ENNReal.ofReal Lambda < ∫⁻ t in Ioc b s, ENNReal.ofReal
          (metricScalarAt (g t) ((Ξ ∘ alpha) t) +
            (g t).inner ((Ξ ∘ alpha) t)
              (lVelocity (Ξ ∘ alpha) t) (lVelocity (Ξ ∘ alpha) t)) := by
  obtain ⟨theta,r,eta,htheta,hr,heta,hmodel⟩ :=
    exists_unweighted_action_lower_bound_of_standard_metric_approximation Lambda hLambda
  refine ⟨theta,r,eta,htheta,hr,heta,?_⟩
  intro N _ _ _ _ Q U g Ξ hΞ alpha b s q hq hbs horizon halpha hclose halt
  have hclock : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun t : ℝ => b + t / q) :=
    (contDiff_const.add (contDiff_id.div_const q)).contMDiff
  have hclockMaps : MapsTo (fun t : ℝ => b + t / q) (Icc 0 (q * (s - b))) (Icc b s) := by
    intro t ht
    refine ⟨le_add_of_nonneg_right (div_nonneg ht.1 hq.le), ?_⟩
    have hh : t / q ≤ s - b := (div_le_iff₀ hq).mpr (by nlinarith [ht.2])
    linarith
  have hbeta : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1
      (fun t => alpha (b + t / q)) (Icc 0 (q * (s - b))) :=
    halpha.comp hclock.contMDiffOn hclockMaps
  have hend : b + q * (s - b) / q = s := by field_simp; ring
  have hlarge := hmodel Q U
    (fun t => localPullMetric (scaleMetric q hq (g (b + t / q))) Ξ hΞ)
    (fun t => alpha (b + t / q)) (q * (s - b))
    (mul_pos hq (sub_pos.mpr hbs)) horizon hbeta hclose
    (by simpa only [zero_div, add_zero, hend] using halt)
  simp_rw [localPullMetric_scaleMetric] at hlarge
  rw [unweighted_action_parabolic_rescaling (fun t => localPullMetric (g t) Ξ hΞ)
    alpha b s q hq] at hlarge
  rw [unweighted_action_localPullback_of_contMDiffOn g Ξ hΞ alpha b s halpha] at hlarge
  exact hlarge

theorem exists_unweighted_action_lower_bound_of_rescaled_standard_metric_approximation_of_ball_exit
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N],
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (Ξ : U → N)
        (hΞ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Ξ)
        (alpha : ℝ → U) (b s q : ℝ) (hq : 0 < q),
        b < s → q * (s - b) ≤ theta →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 alpha (Icc b s) →
        (∀ t ∈ Icc 0 (q * (s - b)), ∀ j : ℕ, j ≤ 2 →
          metricDerivNorm j (localPullMetric (scaleMetric q hq (g (b + t / q))) Ξ hΞ)
            ((Q.val.metric t).restrictOpen U) (StandardCap.metric.restrictOpen U)
            (alpha (b + t / q)) ≤ eta) →
        riemannianEDistOf StandardCap.metric 0 (alpha b).val ≤ ENNReal.ofReal r →
        (q * (s - b) = theta ∨
          ENNReal.ofReal (2 * r) ≤ riemannianEDistOf StandardCap.metric 0 (alpha s).val) →
        ENNReal.ofReal Lambda < ∫⁻ t in Ioc b s, ENNReal.ofReal
          (metricScalarAt (g t) ((Ξ ∘ alpha) t) +
            (g t).inner ((Ξ ∘ alpha) t)
              (lVelocity (Ξ ∘ alpha) t) (lVelocity (Ξ ∘ alpha) t)) := by
  obtain ⟨theta, r, eta, htheta, hr, heta, hb⟩ :=
    exists_unweighted_action_lower_bound_of_rescaled_standard_metric_approximation Lambda hLambda
  refine ⟨theta, r, eta, htheta, hr, heta, ?_⟩
  intro N _ _ _ _ Q U g Ξ hΞ alpha b s q hq hbs horizon halpha hclose hstart halt
  apply hb N Q U g Ξ hΞ alpha b s q hq hbs horizon halpha hclose
  exact halt.imp id (fun hfar => standard_endpoint_separation_of_ball_exit hr.le
    (alpha b).val (alpha s).val hstart hfar)


theorem exists_lRegularizedAction_lower_bound_of_rescaled_standard_metric_approximation
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N],
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := 𝓡 3) (M := N) D)
        (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (Ξ : U → N) (hΞ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Ξ)
        (alpha : ℝ → U) (T b s q : ℝ) (hq : 0 < q),
        b < s → s < T → q * (s - b) ≤ theta →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 alpha
          (Icc (Real.sqrt (T - s)) (Real.sqrt (T - b))) →
        IntervalIntegrable (lRegularizedLagrangian S T (Ξ ∘ alpha)) volume
          (Real.sqrt (T - s)) (Real.sqrt (T - b)) →
        (∀ t ∈ Icc 0 (q * (s - b)), ∀ j : ℕ, j ≤ 2 →
          metricDerivNorm j (localPullMetric (scaleMetric q hq (S.base.metric (b + t / q))) Ξ hΞ)
            ((Q.val.metric t).restrictOpen U) (StandardCap.metric.restrictOpen U)
            (alpha (Real.sqrt (T - (b + t / q)))) ≤ eta) →
        (q * (s - b) = theta ∨
          ENNReal.ofReal r ≤ riemannianEDistOf StandardCap.metric
            (alpha (Real.sqrt (T - b))).val (alpha (Real.sqrt (T - s))).val) →
        Real.sqrt (T - s) * Lambda <
          lRegularizedAction S T (Ξ ∘ alpha)
            (Real.sqrt (T - s)) (Real.sqrt (T - b)) := by
  obtain ⟨theta, r, eta₁, htheta, hr, heta₁, haction⟩ :=
    exists_unweighted_action_lower_bound_of_rescaled_standard_metric_approximation Lambda hLambda
  obtain ⟨eta₂, heta₂, hcompare⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison theta htheta.1.le htheta.2
  refine ⟨theta, r, min eta₁ eta₂, htheta, hr, lt_min heta₁ heta₂, ?_⟩
  intro N _ _ _ _ D S Q U Ξ hΞ alpha T b s q hq hbs hsT horizon halpha hint hclose halt
  let beta := fun t => alpha (Real.sqrt (T - t))
  have hclock : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (fun t : ℝ => Real.sqrt (T - t)) (Icc b s) := by
    have hnonzero : ∀ t ∈ Icc b s, T - t ≠ 0 := fun t ht =>
      ne_of_gt (sub_pos.mpr (ht.2.trans_lt hsT))
    exact ((contDiffOn_const.sub contDiffOn_id).sqrt hnonzero).contMDiffOn
  have hclockMaps : MapsTo (fun t : ℝ => Real.sqrt (T - t)) (Icc b s)
      (Icc (Real.sqrt (T - s)) (Real.sqrt (T - b))) := by
    intro t ht
    exact ⟨Real.sqrt_le_sqrt (sub_le_sub_left ht.2 T),
      Real.sqrt_le_sqrt (sub_le_sub_left ht.1 T)⟩
  have hbeta : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 beta (Icc b s) :=
    halpha.comp hclock hclockMaps
  have hlarge := haction N Q U S.base.metric Ξ hΞ beta b s q hq hbs horizon hbeta
    (fun t ht j hj => (hclose t ht j hj).trans (min_le_left _ _)) halt
  have hscalar : ∀ t ∈ Ioo b s, 0 ≤ S.scalar t ((Ξ ∘ alpha) (Real.sqrt (T - t))) := by
    intro t ht
    let z := q * (t - b)
    have hzage : z ∈ Icc 0 (q * (s - b)) :=
      ⟨mul_nonneg hq.le (sub_nonneg.mpr ht.1.le),
        mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le b) hq.le⟩
    have hztheta : z ∈ Icc 0 theta := ⟨hzage.1, hzage.2.trans horizon⟩
    have hclockeq : b + z / q = t := by dsimp only [z]; field_simp; ring
    have hjets : ∀ j : ℕ, j ≤ 2 →
        metricDerivNorm j (localPullMetric (scaleMetric q hq (S.base.metric t)) Ξ hΞ)
          ((Q.val.metric z).restrictOpen U) (StandardCap.metric.restrictOpen U)
          (alpha (Real.sqrt (T - t))) ≤ eta₂ := by
      intro j hj
      have hh := (hclose z hzage j hj).trans (min_le_right _ _)
      rwa [hclockeq] at hh
    have hsc := (hcompare Q U (localPullMetric (scaleMetric q hq (S.base.metric t)) Ξ hΞ)
      z hztheta (alpha (Real.sqrt (T - t))) hjets).2
    obtain ⟨c, hc, hstandard⟩ := exists_standard_scalar_lower_bound
    have hstd : 0 ≤ metricScalarAt ((Q.val.metric z).restrictOpen U)
        (alpha (Real.sqrt (T - t))) := by
      rw [metricScalarAt_restrictOpen]
      exact (div_nonneg hc.le (sub_nonneg.mpr (hztheta.2.trans htheta.2.le))).trans
        (hstandard Q (alpha (Real.sqrt (T - t))).val z
          ⟨hztheta.1, hztheta.2.trans_lt htheta.2⟩)
    have hscaled := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hstd).trans hsc
    rw [metricScalarAt_localPull, metricScalarAt_scaleMetric] at hscaled
    have hnonneg := nonneg_of_mul_nonneg_right hscaled (inv_pos.mpr hq)
    exact hnonneg
  have hweighted := sqrt_mul_unweighted_action_le_lRegularizedAction S T b s hbs.le hsT.le
    (Ξ ∘ alpha) hint hscalar
  have hsqrt : 0 < Real.sqrt (T - s) := Real.sqrt_pos.mpr (sub_pos.mpr hsT)
  have hstrict := ENNReal.mul_lt_mul_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt)) ENNReal.ofReal_ne_top hlarge
  rw [← ENNReal.ofReal_mul hsqrt.le] at hstrict
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp (hstrict.trans_le hweighted)).1

theorem exists_uniform_disjointness_of_standard_metric_approximation_of_curvature_bound
    (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ c eta : ℝ, 0 < c ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric (𝓡 3) M) (q : ℝ) (hq : 0 < q)
        (Q : StandardSolution) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)))
        (Φ : U → M) (hΦ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Φ)
        (t : ℝ), t ∈ Icc 0 T →
      (∀ x : U, ∀ j : ℕ, j ≤ 2 →
        metricDerivNorm j (localPullMetric (scaleMetric q hq g) Φ hΦ)
          ((Q.val.metric t).restrictOpen U) (StandardCap.metric.restrictOpen U) x ≤ eta) →
      ∀ (K : Set M) (C : ℝ), 9 * Real.sqrt C < c * q →
      (∀ x ∈ K, normSq0S g x 4 (metricRm04At g x) ≤ C) →
      Disjoint (range Φ) K := by
  obtain ⟨eta, heta, hcompare⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison T hT hT1
  obtain ⟨c, hc, hstandard⟩ := exists_standard_scalar_lower_bound
  refine ⟨c / 2, eta, by positivity, heta, ?_⟩
  intro M _ _ _ _ g q hq Q U Φ hΦ t ht hclose K C hscale hRm
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hx
  have hstd : c ≤ metricScalarAt ((Q.val.metric t).restrictOpen U) x := by
    rw [metricScalarAt_restrictOpen]
    apply (le_div_self hc.le (sub_pos.mpr (ht.2.trans_lt hT1)) (sub_le_self 1 ht.1)).trans
    exact hstandard Q x.val t ⟨ht.1, ht.2.trans_lt hT1⟩
  have hsc := (hcompare Q U (localPullMetric (scaleMetric q hq g) Φ hΦ) t ht x (hclose x)).2
  rw [metricScalarAt_localPull, metricScalarAt_scaleMetric, ← div_eq_inv_mul] at hsc
  have hlo : (c / 2) * q ≤ metricScalarAt g (Φ x) := by
    apply (le_div_iff₀ hq).mp
    linarith
  have hd : Module.finrank ℝ (TangentSpace (𝓡 3) (Φ x)) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  have hu : metricScalarAt g (Φ x) ≤ 9 * Real.sqrt C := by
    have hb := scalar_abs_le_rm g (Φ x)
    rw [hd] at hb
    norm_num only [Nat.cast_ofNat, Nat.ofNat_pos, pow_succ, pow_zero, mul_one] at hb
    exact (le_abs_self _).trans (hb.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hRm (Φ x) hx)) (by norm_num)))
  exact (not_lt_of_ge (hlo.trans hu)) hscale

end DifferentialGeometry.PDE.RicciFlow
