import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Neck.SpatialChart

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x y : M}

theorem SpatialNeck.edist_lower_bound_of_scalar_gt
    (nk : SpatialNeck g eps x)
    (hy : (1 + 4323 * eps) * metricScalarAt g x < metricScalarAt g y) :
    ENNReal.ofReal (eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x)) ≤
      riemannianEDistOf g x y := by
  have hexcluded : y ∉ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    intro hmem
    exact hy.not_ge (nk.scalar_bounds_on_image_window hmem).2
  have hb (r : ℝ) (hr : 0 < r) (heps : r < eps⁻¹) :
      ENNReal.ofReal (r * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x)) ≤
        riemannianEDistOf g x y := by
    apply le_of_not_gt
    intro hdist
    apply hexcluded
    obtain ⟨z, hz, rfl⟩ := nk.ball_subset_image_slab hr heps hdist
    exact ⟨z, ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩
  have hlim : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x)))
      (𝓝[<] eps⁻¹) (𝓝 (ENNReal.ofReal (eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x)))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _).div_const _)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (inv_pos.mpr nk.eps_pos)] with r hr
  exact hb r hr.1 hr.2

universe u

theorem endpoint_distance_lower_bound_of_spatial_necks_of_scalar_tendsto_atTop
    (M : ℕ → Type u) [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace ThreeSpace (M n)]
    [∀ n, IsManifold I3 ∞ (M n)] [∀ n, T2Space (M n)]
    (g : ∀ n, SmoothRiemannianMetric I3 (M n)) (x y : ∀ n, M n)
    {eps R d : ℝ} (hR : 0 < R)
    (hnecks : ∀ᶠ n in atTop, Nonempty (SpatialNeck (g n) eps (x n)))
    (hx : Tendsto (fun n => metricScalarAt (g n) (x n)) atTop (𝓝 R))
    (hy : Tendsto (fun n => metricScalarAt (g n) (y n)) atTop atTop)
    (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 d))
    (hdist : ∀ᶠ n in atTop, riemannianEDistOf (g n) (x n) (y n) ≤ ENNReal.ofReal (ell n)) :
    eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt R ≤ d := by
  obtain ⟨n, hn⟩ := hnecks.exists
  obtain ⟨nk⟩ := hn
  have heps := nk.eps_pos
  have heps1 : eps < 1 := nk.eps_small.trans (by norm_num)
  have hfactor : 0 < 1 + 4323 * eps := by positivity
  have hhigh := hy.eventually_gt_atTop ((1 + 4323 * eps) * (R + 1))
  have hlow := hx.eventually (Iio_mem_nhds (lt_add_one R))
  have hsep : ∀ᶠ n in atTop,
      ENNReal.ofReal (eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt (g n) (x n))) ≤
        ENNReal.ofReal (ell n) := by
    filter_upwards [hnecks, hdist, hhigh, hlow] with n hn hd hb ha
    obtain ⟨nk⟩ := hn
    exact (nk.edist_lower_bound_of_scalar_gt
      ((mul_lt_mul_of_pos_left ha hfactor).trans hb)).trans hd
  have hleft : Tendsto (fun n => ENNReal.ofReal
      (eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt (g n) (x n)))) atTop
      (𝓝 (ENNReal.ofReal (eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt R))) := by
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.div
      (Real.continuous_sqrt.tendsto R |>.comp hx) (Real.sqrt_pos.mpr hR).ne')
  have hright := ENNReal.tendsto_ofReal hell
  have hlim := le_of_tendsto_of_tendsto hleft hright hsep
  have hnum : 0 < eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt R := by positivity
  have hd : 0 < d := ENNReal.ofReal_pos.mp ((ENNReal.ofReal_pos.mpr hnum).trans_le hlim)
  exact (ENNReal.ofReal_le_ofReal_iff hd.le).mp hlim


private theorem window_radius_lt_half_neck_depth
    {eps alpha : ℝ} (heps : 0 < eps)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hsmall : 64 * eps ≤ alpha) :
    2 * ((alpha⁻¹ + 6) * Real.sqrt (1 + eps)) < eps⁻¹ * Real.sqrt (1 - eps) := by
  have heps1 : eps < 1 / 11 := by linarith
  have hplus : Real.sqrt (1 + eps) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> linarith
  have hminus : 1 / 2 < Real.sqrt (1 - eps) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - eps by linarith)
    nlinarith [Real.sqrt_nonneg (1 - eps)]
  have hinv : alpha⁻¹ ≤ (64 * eps)⁻¹ := inv_anti₀ (by positivity) hsmall
  have halphainv : 1 ≤ alpha⁻¹ := (one_le_inv₀ halpha).mpr halpha1
  have hnum : 2 * ((alpha⁻¹ + 6) * Real.sqrt (1 + eps)) ≤ 28 * alpha⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hplus (show 0 ≤ alpha⁻¹ + 6 by positivity)
    nlinarith
  have hconst : 28 * (64 * eps)⁻¹ < eps⁻¹ / 2 := by
    field_simp
    nlinarith
  calc
    _ ≤ 28 * alpha⁻¹ := hnum
    _ ≤ 28 * (64 * eps)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ < eps⁻¹ / 2 := hconst
    _ < eps⁻¹ * Real.sqrt (1 - eps) := by
      have h := mul_lt_mul_of_pos_left hminus (inv_pos.mpr heps)
      linarith


theorem eventually_spatial_neck_window_subset_inner_ball_of_endpoint_blowup
    (M : ℕ → Type u) [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace ThreeSpace (M n)]
    [∀ n, IsManifold I3 ∞ (M n)] [∀ n, T2Space (M n)]
    (g : ∀ n, SmoothRiemannianMetric I3 (M n)) (base x y : ∀ n, M n)
    {eps alpha R rho t : ℝ} (halpha1 : alpha ≤ 1)
    (hsmall : 64 * eps ≤ alpha) (hR : 0 < R) (ht : 0 ≤ t) (htrho : t < rho)
    (hnecks : ∀ᶠ n in atTop, Nonempty (SpatialNeck (g n) eps (x n)))
    (hx : Tendsto (fun n => metricScalarAt (g n) (x n)) atTop (𝓝 R))
    (hy : Tendsto (fun n => metricScalarAt (g n) (y n)) atTop atTop)
    (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (hdist : ∀ᶠ n in atTop, riemannianEDistOf (g n) (x n) (y n) ≤ ENNReal.ofReal (ell n - t))
    (hbase : ∀ᶠ n in atTop, riemannianEDistOf (g n) (base n) (x n) ≤ ENNReal.ofReal t) :
    ∃ r : ℝ, t < r ∧ r < rho ∧ ∀ᶠ n in atTop,
      ∀ nk : SpatialNeck (g n) eps (x n),
        nk.map '' (univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) ⊆
          riemannianBallOf (g n) (base n) r := by
  obtain ⟨n, hn⟩ := hnecks.exists
  obtain ⟨nk⟩ := hn
  have heps := nk.eps_pos
  have halpha : 0 < alpha := (by positivity : 0 < 64 * eps).trans_le hsmall
  have hepsalpha : eps < alpha := by linarith
  have hdepth := endpoint_distance_lower_bound_of_spatial_necks_of_scalar_tendsto_atTop
    M g x y hR hnecks hx hy (fun n => ell n - t) (hell.sub_const t) hdist
  let W : ℝ := (alpha⁻¹ + 6) * Real.sqrt (1 + eps)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hhalf : W / Real.sqrt R < (rho - t) / 2 := by
    have hnum := window_radius_lt_half_neck_depth heps halpha halpha1 hsmall
    have hh := (div_lt_div_of_pos_right hnum (Real.sqrt_pos.mpr hR)).trans_le hdepth
    rw [mul_div_assoc] at hh
    dsimp only [W]
    linarith
  let r : ℝ := t + 3 * (rho - t) / 4
  have htr : t < r := by dsimp only [r]; linarith
  have hrrho : r < rho := by dsimp only [r]; linarith
  have hspace : t + W / Real.sqrt R < r := by dsimp only [r]; linarith
  have hwidth : Tendsto (fun n => t + W / Real.sqrt (metricScalarAt (g n) (x n))) atTop
      (𝓝 (t + W / Real.sqrt R)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div
      (Real.continuous_sqrt.tendsto R |>.comp hx) (Real.sqrt_pos.mpr hR).ne')
  refine ⟨r, htr, hrrho, ?_⟩
  filter_upwards [hbase, hwidth.eventually (Iio_mem_nhds hspace)] with n hn hwidthn
  intro nk z hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hlen : alpha⁻¹ < eps⁻¹ := inv_strictAnti₀ heps hepsalpha
  have hslab := nk.image_slab_subset_closedBall (inv_nonneg.mpr halpha.le) hlen
    ⟨w, ⟨hw.1, hw.2.1.le, hw.2.2.le⟩, rfl⟩
  change riemannianEDistOf (g n) (base n) (nk.map w) < ENNReal.ofReal r
  calc
    _ ≤ riemannianEDistOf (g n) (base n) (x n) + riemannianEDistOf (g n) (x n) (nk.map w) :=
      riemannianEDistOf_triangle (g n) _ _ _
    _ ≤ ENNReal.ofReal t + ENNReal.ofReal (W / Real.sqrt (metricScalarAt (g n) (x n))) :=
      add_le_add hn hslab
    _ = ENNReal.ofReal (t + W / Real.sqrt (metricScalarAt (g n) (x n))) :=
      (ENNReal.ofReal_add ht (by positivity)).symm
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff (ht.trans_lt htr)).mpr hwidthn

section

variable {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
  {ι : Type*} {l : Filter ι} [l.NeBot] {y : ι → M} {q : UniformSpace.Completion M}

theorem SpatialNeck.completion_dist_lower_bound_of_scalar_tendsto_atTop
    (nk : SpatialNeck g eps x)
    (hmetric : ∀ u v : M, edist u v = riemannianEDistOf g u v)
    (hy : Tendsto (fun i => (y i : UniformSpace.Completion M)) l (𝓝 q))
    (hscalar : Tendsto (fun i => metricScalarAt g (y i)) l atTop) :
    eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x) ≤
      dist (x : UniformSpace.Completion M) q := by
  have hsep : ∀ᶠ i in l,
      eps⁻¹ * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g x) ≤ dist x (y i) := by
    filter_upwards [hscalar.eventually_gt_atTop ((1 + 4323 * eps) * metricScalarAt g x)] with i hi
    have hbound := nk.edist_lower_bound_of_scalar_gt hi
    rw [← hmetric, edist_dist] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hbound
  apply ge_of_tendsto ((tendsto_const_nhds (x := (x : UniformSpace.Completion M))).dist hy)
  simpa only [UniformSpace.Completion.dist_eq] using hsep

theorem SpatialNeck.scalar_mul_completion_dist_sq_lower_bound_of_scalar_tendsto_atTop
    (nk : SpatialNeck g eps x)
    (hmetric : ∀ u v : M, edist u v = riemannianEDistOf g u v)
    (hy : Tendsto (fun i => (y i : UniformSpace.Completion M)) l (𝓝 q))
    (hscalar : Tendsto (fun i => metricScalarAt g (y i)) l atTop) :
    (eps⁻¹) ^ 2 * (1 - eps) ≤
      metricScalarAt g x * dist (x : UniformSpace.Completion M) q ^ 2 := by
  have heps1 : eps < 1 := nk.eps_small.trans (by norm_num)
  have hroot := (div_le_iff₀ (Real.sqrt_pos.mpr nk.Q_pos)).mp
    (nk.completion_dist_lower_bound_of_scalar_tendsto_atTop hmetric hy hscalar)
  have hsq := pow_le_pow_left₀
    (mul_nonneg (inv_nonneg.mpr nk.eps_pos.le) (Real.sqrt_nonneg (1 - eps))) hroot 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - eps),
    Real.sq_sqrt nk.Q_pos.le] at hsq
  simpa only [mul_comm] using hsq

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
