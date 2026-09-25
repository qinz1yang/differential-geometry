import DifferentialGeometry.Geometry.Neck.PointedEndpoint

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {L : PointedRiemannianManifold.{u, 0, 0} I3}
  {f : ℕ → ℕ} {F : PointedRiemannianConvergenceMaps X L f}

theorem eventually_spatial_neck_on_limit_ray_of_source_necks
    (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {alpha rho : ℝ} (halpha : 0 < alpha) (halphaSmall : alpha < 1 / 11)
    (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    (gamma : ∀ n, ℝ → (X.obj (f n)).M)
    (hstart : ∀ n, gamma n 0 = (X.obj (f n)).basepoint)
    (hmin : ∀ n, ∀ s ∈ Icc 0 (ell n), ∀ t ∈ Icc 0 (ell n),
      riemannianEDistOf (X.obj (f n)).metric (gamma n s) (gamma n t) =
        ENNReal.ofReal |s - t|)
    (g : Ico 0 rho → L.M)
    (hconv : ∀ t : Ico 0 rho,
      Tendsto (fun n => (F.partialDiffeomorph n).symm (gamma n t)) atTop (𝓝 (g t)))
    (hblow : Tendsto (fun n => metricScalarAt (X.obj (f n)).metric (gamma n (ell n)))
      atTop atTop)
    (hscalar : Tendsto (fun t => metricScalarAt L.metric (g t))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop)
    (hnecks : ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
      ∀ᶠ n in atTop,
      2 < metricScalarAt (X.obj (f n)).metric (gamma n t) →
      Nonempty (SpatialNeck (X.obj (f n)).metric
        (min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64)) (gamma n t))) :
    ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
      Nonempty (SpatialNeck L.metric alpha (g t)) := by
  filter_upwards [hscalar.eventually_gt_atTop 2, hnecks] with t ht hnecksAt
  have hwithin : ∀ᶠ n in atTop, (t : ℝ) < ell n := hell.eventually (Ioi_mem_nhds t.property.2)
  have hbase : ∀ᶠ n in atTop,
      riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (gamma n t) ≤
        ENNReal.ofReal (t : ℝ) := by
    filter_upwards [hwithin] with n hn
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
    change riemannianEDistOf (X.obj (f n)).metric ((F.partialDiffeomorph n) L.basepoint)
      (gamma n t) ≤ ENNReal.ofReal r
    rw [F.basepoint_map]
    exact hb.trans (ENNReal.ofReal_le_ofReal (by dsimp only [r]; linarith [t.property.2]))
  have hscalarLimit := pointedScalar_tendsto_of_inverse_tendsto C hcanonical
    (fun n => gamma n t) hstay (hconv t)
  have hsourceNecks : ∀ᶠ n in atTop, Nonempty (SpatialNeck (X.obj (f n)).metric
      (min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64)) (gamma n t)) := by
    filter_upwards [hnecksAt, hscalarLimit.eventually (Ioi_mem_nhds ht)] with n hn hR
    exact hn hR
  have hdist : ∀ᶠ n in atTop,
      riemannianEDistOf (X.obj (f n)).metric (gamma n t) (gamma n (ell n)) ≤
        ENNReal.ofReal (ell n - t) := by
    filter_upwards [hwithin] with n hn
    rw [hmin n t ⟨t.property.1, hn.le⟩ (ell n)
      ⟨t.property.1.trans hn.le, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr hn.le), neg_sub]
  exact nonempty_spatial_neck_at_limit_of_endpoint_blowup C hcanonical halpha halphaSmall
    (fun n => gamma n t) (fun n => gamma n (ell n)) (g t) t.property.1 t.property.2
    hcompact ht (hconv t) hblow ell hell hdist hbase hsourceNecks

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
