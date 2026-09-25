import DifferentialGeometry.Geometry.Neck.PointedRay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSegmentNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_spatial_necks_on_limit_segment_of_windowed_models (kappa : ℝ)
    {alpha : ℝ} (halpha : 0 < alpha) (halphaSmall : alpha < 1 / 11) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ X : FlowSequence.{u},
      ∀ (f : ℕ → ℕ) (L : PointedRiemannianManifold.{u, 0, 0} I3)
        (F : PointedRiemannianConvergenceMaps (X.atTime 0) L f)
        (C : MetricConvergenceData F),
      (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) →
      ∀ rho : ℝ, 0 < rho → ∀ ell : ℕ → ℝ, Tendsto ell atTop (𝓝 rho) →
      (∀ R : ℝ, 0 ≤ R → R < rho →
        IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) →
      ∀ gamma : ∀ n, ℝ → (X.term (f n)).M,
      (∀ n, gamma n 0 = (X.term (f n)).basepoint) →
      (∀ n, ∀ s ∈ Icc 0 (ell n), ∀ t ∈ Icc 0 (ell n),
        riemannianEDistOf ((X.term (f n)).S.base.metric 0) (gamma n s) (gamma n t) =
          ENNReal.ofReal |s - t|) →
      ∀ g : Ico 0 rho → L.M,
      (∀ t : Ico 0 rho,
        Tendsto (fun n => (F.partialDiffeomorph n).symm (gamma n t)) atTop (𝓝 (g t))) →
      Tendsto (fun n => (X.term (f n)).S.scalar 0 (gamma n (ell n))) atTop atTop →
      Tendsto (fun t => metricScalarAt L.metric (g t))
        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop →
      ∀ eps : ℝ, eps ≤ epsStar →
      (∀ t : Ico 0 rho, ∀ᶠ n in atTop,
        2 ≤ (X.term (f n)).S.scalar 0 (gamma n t) → ∃ W : WindowedModelWitness eps kappa (X.term (f n)).S (gamma n t) 0,
          (∀ s ∈ Ioo (-modelDepth eps) 0,
            parabolicTime 0 ((X.term (f n)).S.scalar 0 (gamma n t)) s ∈
              (X.interval (f n)).regular) ∧
          Nonempty (TangentOrientationSection W.model.M)) →
      ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
        Nonempty (SpatialNeck L.metric alpha (g t)) := by
  let beta := min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64)
  have hbeta : 0 < beta := lt_min (neckModelTolerance_pos (by positivity)) (by positivity)
  have hbetaSmall : beta / 2 < 1 / 32 := by
    have h := min_le_right (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64)
    dsimp only [beta]
    linarith
  obtain ⟨epsStar, hepsStar, hsource⟩ :=
    exists_eventually_windowed_strongNeck_near_scalar_blowup_endpoint.{u} kappa
      (alpha := beta / 2) (by positivity) hbetaSmall
  refine ⟨epsStar, hepsStar, ?_⟩
  intro X f L F C hcanonical rho hrho ell hell hcompact gamma hstart hmin g hconv
    hblow hscalar eps heps hgood
  have hsourceScalar (t : Ico 0 rho) : Tendsto
      (fun n => (X.term (f n)).S.scalar 0 (gamma n t)) atTop
      (𝓝 (metricScalarAt L.metric (g t))) := by
    have hwithin : ∀ᶠ n in atTop, (t : ℝ) < ell n := hell.eventually (Ioi_mem_nhds t.property.2)
    have hbase : ∀ᶠ n in atTop,
        riemannianEDistOf ((X.atTime 0).obj (f n)).metric ((X.atTime 0).obj (f n)).basepoint (gamma n t) ≤
          ENNReal.ofReal (t : ℝ) := by
      filter_upwards [hwithin] with n hn
      change riemannianEDistOf ((X.term (f n)).S.base.metric 0)
        (X.term (f n)).basepoint (gamma n t) ≤ ENNReal.ofReal (t : ℝ)
      rw [← hstart n, hmin n 0 ⟨le_rfl, t.property.1.trans hn.le⟩ t ⟨t.property.1, hn.le⟩]
      simp only [zero_sub, abs_neg, abs_of_nonneg t.property.1, le_refl]
    have hstay : ∀ᶠ n in atTop, gamma n t ∈ F.target n := by
      let r := ((t : ℝ) + rho) / 2
      let R := (r + rho) / 2
      let factor := (r + R) / (2 * r)
      have hr : 0 < r := by dsimp only [r]; linarith [t.property.1, t.property.2]
      have hrR : r < R := by dsimp only [R, r]; linarith [t.property.2]
      have hRrho : R < rho := by dsimp only [R, r]; linarith [t.property.2]
      have hfactor : 1 < factor := by
        dsimp only [factor]
        apply (lt_div_iff₀ (by positivity)).mpr
        linarith
      have hbuffer : factor * r < R := by
        have heq : factor * r = (r + R) / 2 := by dsimp only [factor]; field_simp
        rw [heq]
        linarith
      have hc := hcompact R (hr.trans hrR).le hRrho
      have hm : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F)
          (riemannianClosedBallOf L.metric L.basepoint R) 0 := by
        rw [← funext hcanonical]
        exact C.converges _ hc 0
      filter_upwards [pointed_metric_eventually_inverse_ball_capture L.basepoint hr.le
        hfactor hbuffer hc hm, hbase] with n hn hb
      apply (hn.2 (gamma n t) ?_).1
      change riemannianEDistOf ((X.atTime 0).obj (f n)).metric ((F.partialDiffeomorph n) L.basepoint)
        (gamma n t) ≤ ENNReal.ofReal r
      rw [F.basepoint_map]
      exact hb.trans (ENNReal.ofReal_le_ofReal (by dsimp only [r]; linarith [t.property.2]))
    exact pointedScalar_tendsto_of_inverse_tendsto C hcanonical
      (fun n => gamma n t) hstay (hconv t)
  have hgood' (t : Ico 0 rho) (ht : 2 < metricScalarAt L.metric (g t)) :
      ∀ᶠ n in atTop, ∃ W : WindowedModelWitness eps kappa (X.term (f n)).S (gamma n t) 0,
        (∀ s ∈ Ioo (-modelDepth eps) 0,
          parabolicTime 0 ((X.term (f n)).S.scalar 0 (gamma n t)) s ∈
            (X.interval (f n)).regular) ∧ Nonempty (TangentOrientationSection W.model.M) := by
    filter_upwards [hgood t, (hsourceScalar t).eventually (Ioi_mem_nhds ht)] with n hn hR
    exact hn hR.le
  have hneck := hsource (fun n => (X.term (f n)).M)
    (fun n => X.interval (f n)) (fun n => (X.term (f n)).S)
    (fun n => (X.term (f n)).isSolution) eps heps (fun _ => 0) gamma ell rho hrho hell
    (fun t => metricScalarAt L.metric (g t)) hmin hsourceScalar hscalar hblow hgood'
  have hspatial : ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
      ∀ᶠ n in atTop, 2 < metricScalarAt ((X.atTime 0).obj (f n)).metric (gamma n t) →
        Nonempty (SpatialNeck ((X.atTime 0).obj (f n)).metric beta (gamma n t)) := by
    filter_upwards [hneck] with t ht
    filter_upwards [ht] with n hn
    intro _
    obtain ⟨nk⟩ := hn
    have nk' := nk.toSpatialNeck
    change Nonempty (SpatialNeck ((X.term (f n)).S.base.metric 0) beta (gamma n t))
    simpa only [mul_div_cancel₀ beta (by norm_num : (2 : ℝ) ≠ 0)] using
      (show Nonempty (SpatialNeck ((X.term (f n)).S.base.metric 0)
        (2 * (beta / 2)) (gamma n t)) from ⟨nk'⟩)
  exact eventually_spatial_neck_on_limit_ray_of_source_necks C hcanonical halpha halphaSmall
    ell hell hcompact gamma hstart hmin g hconv hblow hscalar hspatial

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
