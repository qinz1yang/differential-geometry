import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.InverseSpatialNeckTransfer
import DifferentialGeometry.Geometry.Neck.ScalarSeparation
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} I3} {L : PointedRiemannianManifold.{u, 0, 0} I3}
  {f : ℕ → ℕ} {F : PointedRiemannianConvergenceMaps X L f}

theorem nonempty_spatial_neck_at_limit_of_endpoint_blowup
    (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {alpha : ℝ} (halpha : 0 < alpha) (halphaSmall : alpha < 1 / 11)
    (x y : ∀ n, (X.obj (f n)).M) (z : L.M)
    {rho t : ℝ} (ht : 0 ≤ t) (htrho : t < rho)
    (hcompact : ∀ r : ℝ, 0 ≤ r → r < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint r))
    (hscalar : 2 < metricScalarAt L.metric z)
    (hconv : Tendsto (fun n => (F.partialDiffeomorph n).symm (x n)) atTop (𝓝 z))
    (hy : Tendsto (fun n => metricScalarAt (X.obj (f n)).metric (y n)) atTop atTop)
    (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (hdist : ∀ᶠ n in atTop, riemannianEDistOf (X.obj (f n)).metric (x n) (y n) ≤
      ENNReal.ofReal (ell n - t))
    (hbase : ∀ᶠ n in atTop, riemannianEDistOf (X.obj (f n)).metric
      (X.obj (f n)).basepoint (x n) ≤ ENNReal.ofReal t)
    (hnecks : ∀ᶠ n in atTop, Nonempty (SpatialNeck (X.obj (f n)).metric
      (min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64)) (x n))) :
    Nonempty (SpatialNeck L.metric alpha z) := by
  let beta := alpha / 26000
  let eps := min (neckModelTolerance beta) (beta / 64)
  have hbeta : 0 < beta := div_pos halpha (by norm_num)
  have hbetaSmall : 2 * beta < 1 / 11 := by dsimp only [beta]; linarith
  have heps : 0 < eps := lt_min (neckModelTolerance_pos hbeta) (by dsimp only [beta]; positivity)
  have hsmall : 64 * eps ≤ beta := by
    have hh : eps ≤ beta / 64 := min_le_right _ _
    linarith
  have hstay : ∀ᶠ n in atTop, x n ∈ F.target n := by
    let r₀ := (t + rho) / 2
    let R₀ := (r₀ + rho) / 2
    let factor₀ := (r₀ + R₀) / (2 * r₀)
    have hr₀ : 0 < r₀ := by dsimp only [r₀]; linarith
    have hR₀ : r₀ < R₀ := by dsimp only [R₀, r₀]; linarith
    have hR₀rho : R₀ < rho := by dsimp only [R₀, r₀]; linarith
    have hf₀ : 1 < factor₀ := by
      dsimp only [factor₀]
      apply (lt_div_iff₀ (by positivity)).mpr
      linarith
    have hbuf₀ : factor₀ * r₀ < R₀ := by
      have heq : factor₀ * r₀ = (r₀ + R₀) / 2 := by dsimp only [factor₀]; field_simp
      rw [heq]
      linarith
    have hc₀ := hcompact R₀ (hr₀.trans hR₀).le hR₀rho
    have hmetric : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F)
        (riemannianClosedBallOf L.metric L.basepoint R₀) 0 := by
      have heq : C.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact C.converges _ hc₀ 0
    filter_upwards [pointed_metric_eventually_inverse_ball_capture L.basepoint hr₀.le hf₀ hbuf₀
      hc₀ hmetric, hbase] with n hn hb
    have hball : x n ∈ riemannianClosedBallOf (X.obj (f n)).metric (F.map n L.basepoint) r₀ := by
      change x n ∈ riemannianClosedBallOf (X.obj (f n)).metric ((F.partialDiffeomorph n) L.basepoint) r₀
      rw [F.basepoint_map]
      exact hb.trans (ENNReal.ofReal_le_ofReal (by dsimp only [r₀]; linarith))
    exact (hn.2 (x n) hball).1
  have hscalarLimit := pointedScalar_tendsto_of_inverse_tendsto C hcanonical x hstay hconv
  obtain ⟨r, htr, hrho, hwindow⟩ :=
    eventually_spatial_neck_window_subset_inner_ball_of_endpoint_blowup
      (fun n => (X.obj (f n)).M) (fun n => (X.obj (f n)).metric)
      (fun n => (X.obj (f n)).basepoint) x y
      (show beta ≤ 1 by dsimp only [beta]; linarith) hsmall
      (show 0 < metricScalarAt L.metric z by linarith) ht htrho hnecks hscalarLimit
      hy ell hell hdist hbase
  have hr : 0 < r := ht.trans_lt htr
  let R := (r + rho) / 2
  let factor := (r + R) / (2 * r)
  have hfactor : 1 < factor := by dsimp only [factor, R]; apply (lt_div_iff₀ (by positivity)).mpr; linarith
  have hbuffer : factor * r < R := by
    have heq : factor * r = (r + R) / 2 := by dsimp only [factor]; field_simp
    rw [heq]
    dsimp only [R]
    linarith
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hRrho : R < rho := by dsimp only [R]; linarith
  have htransfer := eventually_spatialNeck_inverse_transport_of_window_subset_ball C hcanonical
    hbeta hbetaSmall hr.le hfactor hbuffer (hcompact R hR hRrho)
  have hscalarAt : ∀ᶠ n in atTop,
      2 ≤ metricScalarAt L.metric ((F.partialDiffeomorph n).symm (x n)) := by
    have hh := (metricScalar_smooth L.metric).continuous.tendsto z |>.comp hconv
    exact (hh.eventually (Ioi_mem_nhds hscalar)).mono fun _ h => h.le
  have hfixed : ∀ᶠ n in atTop,
      Nonempty (SpatialNeck L.metric (2 * beta) ((F.partialDiffeomorph n).symm (x n))) := by
    filter_upwards [htransfer, hwindow, hnecks, hscalarAt] with n hn hw hnk hRz
    obtain ⟨nk⟩ := hnk
    let nk' := nk.mono (min_le_left (neckModelTolerance beta) (beta / 64))
      ((neckModelTolerance_le beta).trans_lt (by dsimp only [beta]; linarith))
    obtain ⟨_, out, _⟩ := hn (x n) hRz nk' (by
      intro w hw'
      have hm := hw nk ⟨w, hw', rfl⟩
      exact (show riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint (nk.map w) <
        ENNReal.ofReal r from hm).le)
    exact ⟨out⟩
  apply exists_spatial_neck_at_limit_of_tendsto_centers L.metric hconv halphaSmall ?_ hfixed
  dsimp only [beta]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
