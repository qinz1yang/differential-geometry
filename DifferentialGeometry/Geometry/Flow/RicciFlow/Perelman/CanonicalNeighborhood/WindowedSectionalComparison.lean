import DifferentialGeometry.Geometry.Curvature.SectionalPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalScalingTransport

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance sectionalComparisonSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem riemannOp_norm_le_of_rmNormSq_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold I3 ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I3 N) (z : N) {K : ℝ} (hK : 0 ≤ K)
    (hrm : normSq0S g z 4 (metricRm04At g z) ≤ K ^ 2)
    (a b c : TangentSpace I3 z) :
    Real.sqrt (g.inner z (riemannOp (LeviCivita g) z a b c)
      (riemannOp (LeviCivita g) z a b c)) ≤
      K * Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
        Real.sqrt (g.inner z c c) := by
  have hn := riemannOp_normSq_le_of_rmNormSq_le g z hrm a b c
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ K ^ 2 * g.inner z a a * g.inner z b b * g.inner z c c := hn
    _ = _ := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (metric_inner_self_nonneg g z a),
        Real.sq_sqrt (metric_inner_self_nonneg g z b),
        Real.sq_sqrt (metric_inner_self_nonneg g z c)]

omit [SigmaCompactSpace M] in
private theorem windowed_metric_inner_sub_le
    {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    {s : ℝ} (hs : s ∈ Icc (-modelDepth delta) 0)
    {y : sourceOpen W.embedding}
    (hy : (y : W.model.M) ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta)) (v w : TangentSpace I3 y) :
    |(witnessPullbackMetric W.embedding (rescaledMetric S t (S.scalar t x) W.scalar_pos) s).inner
        y v w - (witnessModelMetric W.embedding W.model.S.base.metric s).inner y v w| ≤
      delta * Real.sqrt ((W.model.S.base.metric s).inner (y : W.model.M) v v) *
        Real.sqrt ((W.model.S.base.metric s).inner (y : W.model.M) w w) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (W.model.S.base.metric s) (y : W.model.M)
  have h := abs_apply_le_sqrt_normSq0S (W.model.S.base.metric s) (y : W.model.M) 2
    basis hON (W.comparison.jet 0 s (y : W.model.M))
    (vec2 (I := I3) (x := (y : W.model.M)) v w)
  have hjet : Real.sqrt (normSq0S (W.model.S.base.metric s) (y : W.model.M) 2
      (W.comparison.jet 0 s (y : W.model.M))) ≤ delta :=
    W.comparison.close 0 0 (by omega) s hs (y : W.model.M) hy
  have hprod : (∏ i : Fin 2, Real.sqrt ((W.model.S.base.metric s).inner (y : W.model.M)
      (vec2 (I := I3) (x := (y : W.model.M)) v w i)
      (vec2 (I := I3) (x := (y : W.model.M)) v w i))) =
      Real.sqrt ((W.model.S.base.metric s).inner (y : W.model.M) v v) *
        Real.sqrt ((W.model.S.base.metric s).inner (y : W.model.M) w w) := by
    rw [Fin.prod_univ_two]
    rfl
  rw [hprod, W.comparison.jet_zero, W.comparison.pullback_eq s (y : W.model.M) hy] at h
  rw [witnessPullbackMetric, openPullbackMetric_inner]
  exact h.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hjet
      (mul_nonneg (Real.sqrt_nonneg ((W.model.S.base.metric s).inner (y : W.model.M) v v))
        (Real.sqrt_nonneg ((W.model.S.base.metric s).inner (y : W.model.M) w w))))

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.sectional_lower_bound_on_canonical_domain
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 4) (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hsec : SecLower (W.model.S.base.metric 0) C2⁻¹ K.domain.carrier)
    (hsmall : (1 + delta) * witnessRiemannC delta + delta * C2 ≤ C2⁻¹ / 2) :
    SecLower (S.base.metric t) ((8 * C2)⁻¹ * S.scalar t x)
      (W.embedding '' K.domain.carrier) := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  let F := W.embedding
  let h := W.model.S.base.metric
  let ghat := rescaledMetric S t (S.scalar t x) W.scalar_pos
  let : SigmaCompactSpace (sourceOpen F) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (sourceOpen F).isOpen)
  have hcomplete : RiemannianMetricComplete (h 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hR : 0 < modelRadius delta := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have horder : 2 ≤ modelOrder delta := by
    have hh := five_le_modelOrder W.eps_pos hdelta
    omega
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hpull : SecLower (witnessPullbackMetric F ghat 0) ((8 * C2)⁻¹)
      (Subtype.val ⁻¹' K.domain.carrier) := by
    intro y hy u v
    have hyball := W.canonical_domain_subset_comparison_ball K hbuffer hy
    have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
    have hrm : W.model.rmNormSq 0 (y : W.model.M) ≤ C2 ^ 2 := by
      have hb := K.rm_bound (y : W.model.M) hy
      rw [hbase, mul_one] at hb
      change Real.sqrt (W.model.rmNormSq 0 (y : W.model.M)) ≤ C2 at hb
      have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 (y : W.model.M))
      nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 (y : W.model.M))]
    have hmodelnorm : normSq0S (witnessModelMetric F h 0) y 4
        (metricRm04At (witnessModelMetric F h 0) y) ≤ C2 ^ 2 := by
      rw [witnessModelMetric, rmNormSq_restrictOpen (h 0) (sourceOpen F) y]
      exact hrm
    have hmodel := riemannOp_norm_le_of_rmNormSq_le
      (witnessModelMetric F h 0) y hC2.le hmodelnorm
    have hdiff := W.comparison.riemannOp_sub_norm_le (h 0) hcomplete W.model.basepoint hR
      W.eps_pos.le W.eps_lt_one horder ht0 (y := y) hyball
    have hmet := windowed_metric_inner_sub_le W ht0 hyball
    have hupper : ∀ a : TangentSpace I3 y,
        (witnessPullbackMetric F ghat 0).inner y a a ≤
          2 * (witnessModelMetric F h 0).inner y a a := by
      intro a
      have hb := (W.comparison.equivalence 0 ht0 (y : W.model.M) hyball a).2
      rw [W.comparison.pullback_eq 0 (y : W.model.M) hyball (fun _ => a)] at hb
      rw [witnessPullbackMetric, openPullbackMetric_inner]
      exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : 1 + delta ≤ 2)
        (metric_inner_self_nonneg (witnessModelMetric F h 0) y a))
    have hlower : ∀ a b : TangentSpace I3 y,
        C2⁻¹ * ((witnessModelMetric F h 0).inner y a a *
          (witnessModelMetric F h 0).inner y b b -
          ((witnessModelMetric F h 0).inner y a b) ^ 2) ≤
          metricRm04StandardAt (witnessModelMetric F h 0) y a b b a := by
      intro a b
      rw [witnessModelMetric, metricRm04StandardAt_restrictOpen]
      simp only [mfderiv_subtype_val_apply, SmoothRiemannianMetric.restrictOpen_inner]
      have hvec : vec4 (I := I3) (x := (y : W.model.M)) a b b a =
          (fun i : Fin 4 => ![a, b, b, a] i) := by
        funext i
        fin_cases i <;> rfl
      erw [metricRm04StandardAt_apply, hvec]
      exact hsec (y : W.model.M) hy a b
    have hsmall' : ((1 + delta) * witnessRiemannC delta + delta * C2) +
        (8 * C2)⁻¹ * (2 : ℝ) ^ 2 ≤ C2⁻¹ := by
      have heq : (8 * C2)⁻¹ * (2 : ℝ) ^ 2 = C2⁻¹ / 2 := by
        field_simp
        ring
      rw [heq]
      linarith
    exact metricRm04StandardAt_lower_bound_of_riemannOp_sub_le
      (witnessPullbackMetric F ghat 0) (witnessModelMetric F h 0) y W.eps_pos.le
      (inv_nonneg.mpr (mul_nonneg (by norm_num) hC2.le)) (by norm_num : (0 : ℝ) ≤ 2)
      hmet hdiff hmodel hupper hlower hsmall' u v
  have hsource := W.canonical_domain_subset_source K hbuffer
  have htarget : SecLower (ghat 0) ((8 * C2)⁻¹) (F '' K.domain.carrier) :=
    secLower_image_of_openPullbackMetric F hsource (ghat 0) hpull
  exact (secLower_scaleMetric_iff W.scalar_pos (S.base.metric t)
    (W.embedding '' K.domain.carrier)).mp (by simpa only [ghat, rescaledMetric,
      parabolicTime_zero, F] using htarget)

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.sectional_lower_bound_on_canonical_domain_of_small
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 4) (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hsec : SecLower (W.model.S.base.metric 0) C2⁻¹ K.domain.carrier)
    (hsmall : 2 * C2 * (25 + C2) * delta ≤ 1) :
    SecLower (S.base.metric t) ((8 * C2)⁻¹ * S.scalar t x)
      (W.embedding '' K.domain.carrier) := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  apply W.sectional_lower_bound_on_canonical_domain K hdelta hbuffer hsec
  have hR := witnessRiemannC_le W.eps_pos.le hdelta
  have hprod := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ 1 + delta by linarith [W.eps_pos])
  have hquad : delta ^ 2 ≤ delta / 4 := by
    nlinarith [mul_nonneg W.eps_pos.le (sub_nonneg.mpr hdelta)]
  have herr : (1 + delta) * witnessRiemannC delta + delta * C2 ≤
      (25 + C2) * delta := by nlinarith
  have hbd : (25 + C2) * delta ≤ C2⁻¹ / 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * C2 by positivity)).mp
    have hinv : (2 * C2) * (C2⁻¹ / 2) = 1 := by field_simp
    rw [hinv]
    nlinarith
  exact herr.trans hbd

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
