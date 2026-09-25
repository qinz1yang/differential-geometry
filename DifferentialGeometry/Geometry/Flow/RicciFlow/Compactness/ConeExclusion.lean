import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Geometry.Comparison.Toponogov.PuncturedConeConvergence
import DifferentialGeometry.Geometry.Metric.ConeChart.Construction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeTerminalExclusion

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

variable {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [SigmaCompactSpace M] {W : Type*} [MetricSpace W]

theorem solution_not_rescaled_cone_limit
    {tau : ℝ} (htau : 0 < tau)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closed (-tau) 0 (by linarith)))
    (hS : IsSolutionOn S)
    (hmetric : ∀ a b : M, edist a b = riemannianEDistOf (S.base.metric 0) a b)
    (hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ)
    (p : M) (hscalar : metricScalarAt (S.base.metric 0) p ≠ 0)
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    (x : ℕ → W) (f : ℕ → M → W) (rho : ℕ → ℝ)
    (hrho : ∀ i, 0 < rho i) (hrho0 : Tendsto rho atTop (𝓝 0))
    (hbase : ∀ i, f i p = x i)
    {R lower B : ℝ} (hR : 0 < R) (hlower : 0 < lower)
    (hcompact : IsCompact (Metric.closedBall p R))
    (hcenter : ∀ᶠ i in atTop, dist (x i : UniformSpace.Completion W) q / rho i ∈ Icc lower B)
    (hcover : ∀ᶠ i in atTop, Metric.closedBall (x i) (R / 4 * rho i) ⊆ f i '' Metric.closedBall p R)
    (hdist : ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
      ∀ a ∈ Metric.closedBall p R, ∀ b ∈ Metric.closedBall p R,
        |dist (f i a) (f i b) / rho i - dist a b| < eps) : False := by
  let _ := cone.angles.metricSpace
  obtain ⟨e, hp, hpositive, he⟩ := cone.exists_cone_coordinates_of_rescaled_convergence
    p x f rho hrho hrho0 hbase hR hlower hcompact hcenter hcover hdist
  obtain ⟨U, hpU, _, ⟨chart⟩⟩ := DifferentialGeometry.Geometry.Riemannian.exists_cone_chart_of_coneDistance
    (S.base.metric 0) hmetric e hpositive he (m := 2) (by simp [ThreeSpace]) hp
  exact solution_cone_terminal_exclusion S hS (show -tau < 0 by linarith)
    (subset_refl _) (subset_refl _) U chart
    (fun t ht a _ v w => hsec t ht a (mem_univ _) v w)
    ⟨p, hpU, hscalar⟩

private theorem actual_curvature_scale_bounds
    (Q A d : ℕ → ℝ) (hA : ∀ i, 0 < A i) (hd : ∀ i, 0 ≤ d i)
    (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun i => A i / Q i) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ i in atTop, c ≤ Q i * d i ^ 2)
    (hupper : ∃ B : ℝ, ∀ᶠ i in atTop, Q i * d i ^ 2 ≤ B) :
    Tendsto A atTop atTop ∧ ∃ B : ℝ,
      ∀ᶠ i in atTop, d i / (1 / Real.sqrt (A i)) ∈ Icc (Real.sqrt (c / 2)) B := by
  have hratio' : ∀ᶠ i in atTop, A i / Q i ∈ Ioo (1 / 2) 2 :=
    hratio.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hcompare : ∀ᶠ i in atTop, Q i / 2 ≤ A i ∧ A i ≤ 2 * Q i := by
    filter_upwards [hratio', hQ.eventually_gt_atTop 0] with i hi hQi
    have hl := (lt_div_iff₀ hQi).mp hi.1
    have hu := (div_lt_iff₀ hQi).mp hi.2
    exact ⟨by linarith only [hl], hu.le⟩
  refine ⟨tendsto_atTop_mono' atTop (hcompare.mono fun _ hi => hi.1)
    (Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) hQ), ?_⟩
  obtain ⟨B, hB⟩ := hupper
  refine ⟨Real.sqrt (max 1 (2 * B)) + 1, ?_⟩
  filter_upwards [hcompare, hlower, hB] with i hi hlow hup
  let z := d i / (1 / Real.sqrt (A i))
  have hz : 0 ≤ z := div_nonneg (hd i) (one_div_nonneg.mpr (Real.sqrt_nonneg _))
  have hzsq : z ^ 2 = A i * d i ^ 2 := by
    dsimp [z]
    rw [one_div, div_inv_eq_mul, mul_pow, Real.sq_sqrt (hA i).le]
    ring
  have hc0 : 0 ≤ c := hc.le
  have hlo : c / 2 ≤ z ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hi.1 (sq_nonneg (d i))
    rw [hzsq]
    nlinarith only [hh, hlow, hc0]
  have hup' : z ^ 2 ≤ 2 * B := by
    have hh := mul_le_mul_of_nonneg_right hi.2 (sq_nonneg (d i))
    rw [hzsq]
    nlinarith only [hh, hup]
  have hroot : z ≤ Real.sqrt (max 1 (2 * B)) :=
    Real.le_sqrt_of_sq_le (hup'.trans (le_max_right _ _))
  change z ∈ Icc (Real.sqrt (c / 2)) (Real.sqrt (max 1 (2 * B)) + 1)
  exact ⟨(Real.sqrt_le_iff).mpr ⟨hz, hlo⟩, by linarith only [hroot]⟩

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

theorem riemannian_rescaled_cone_solution_exclusion
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    {q0 : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q0 d)
    (x : ℕ → W) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (hAtop : Tendsto A atTop atTop) (lower B : ℝ) (hlower : 0 < lower)
    (hcenter : ∀ᶠ n in atTop, dist (x n : UniformSpace.Completion W) q0 /
      (1 / Real.sqrt (A n)) ∈ Icc lower B)
    (P : PointedRiemannianManifold.{0, 0, 0} I3) (hpath : PathConnectedSpace P.M)
    (tau : ℝ) (htau : 0 < tau)
    (S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)))
    (C : ℕ → P.M → W) (hS : IsSolutionOn S) (hterminal : S.base.metric 0 = P.metric)
    (hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ)
    (hscalar : metricScalarAt P.metric P.basepoint ≠ 0)
    (hbase : ∀ n, C n P.basepoint = x n)
    (r : ℝ) (hr : 0 < r) (hK : IsCompact (riemannianClosedBallOf P.metric P.basepoint r))
    (hcapture : ∀ᶠ n in atTop,
      riemannianClosedBallOf (scaleMetric (A n) (hA n) gW) (x n) (r / 4) ⊆
        (C n) '' riemannianClosedBallOf P.metric P.basepoint r)
    (hdist : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
      ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
        |metricDistance (scaleMetric (A n) (hA n) gW) (C n a) (C n b) -
          metricDistance P.metric a b| < eta) : False := by
  let H := fun n => scaleMetric (A n) (hA n) gW
  let _ : PathConnectedSpace P.M := hpath
  let _ : PseudoMetricSpace P.M := P.metric.toPseudoMetricSpace
  let _ : MetricSpace P.M := MetricSpace.ofT0PseudoMetricSpace P.M
  have hPmetric : ∀ a b : P.M, edist a b = riemannianEDistOf P.metric a b := fun _ _ => rfl
  let rho := fun n => 1 / Real.sqrt (A n)
  have hrho (n : ℕ) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hA n))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hballP : riemannianClosedBallOf P.metric P.basepoint r = Metric.closedBall P.basepoint r := by
    ext y
    change riemannianEDistOf P.metric P.basepoint y ≤ ENNReal.ofReal r ↔ dist y P.basepoint ≤ r
    rw [← hPmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
  have hballH (n : ℕ) : riemannianClosedBallOf (H n) (x n) (r / 4) =
      Metric.closedBall (x n) (r / 4 * rho n) := by
    have hscale : r / 4 = Real.sqrt (A n) * (r / 4 * rho n) := by
      dsimp [rho]
      field_simp [(Real.sqrt_pos.mpr (hA n)).ne']
    dsimp only [H]
    conv_lhs => rw [hscale]
    rw [riemannianClosedBallOf_scaleMetric]
    ext y
    change riemannianEDistOf gW (x n) y ≤ ENNReal.ofReal (r / 4 * rho n) ↔
      dist y (x n) ≤ r / 4 * rho n
    rw [← hWmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
  have hdistP (a b : P.M) : metricDistance P.metric a b = dist a b := by
    rw [metricDistance, ← hPmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hdistH (n : ℕ) (a b : W) : metricDistance (H n) a b = dist a b / rho n := by
    rw [metricDistance, edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ← hWmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    dsimp [rho]
    rw [one_div, div_inv_eq_mul, mul_comm]
  apply solution_not_rescaled_cone_limit htau S hS
    (fun a b => by rw [hterminal]; exact hPmetric a b) hsec P.basepoint
    (by rw [hterminal]; exact hscalar) cone
    x C rho hrho hrho0 hbase hr hlower
    (by rwa [← hballP]) hcenter
  · filter_upwards [hcapture] with n hn
    have hc := hn
    change riemannianClosedBallOf (H n) (x n) (r / 4) ⊆
      (C n) '' riemannianClosedBallOf P.metric P.basepoint r at hc
    rwa [hballH, hballP] at hc
  · intro eta heta
    filter_upwards [hdist eta heta] with n hn
    intro a ha b hb
    have hh := hn a (hballP.symm ▸ ha) b (hballP.symm ▸ hb)
    change |metricDistance (H n) (C n a) (C n b) - metricDistance P.metric a b| < eta at hh
    rwa [hdistH, hdistP] at hh

theorem rescaled_end_cone_exclusion
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    (gW : SmoothRiemannianMetric I3 W)
    (hWmetric : ∀ a b : W, edist a b = riemannianEDistOf gW a b)
    {q0 : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q0 d)
    (x : ℕ → W) (j : ℕ → ℕ) (hj : StrictMono j) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (Q : ℕ → ℝ) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun n => A n / Q (j n)) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ n in atTop, c ≤ Q n * dist (x n : UniformSpace.Completion W) q0 ^ 2)
    (hupper : ∃ B : ℝ, ∀ᶠ n in atTop, Q n * dist (x n : UniformSpace.Completion W) q0 ^ 2 ≤ B)
    (P : PointedRiemannianManifold.{0, 0, 0} I3) (hpath : PathConnectedSpace P.M)
    (tau : ℝ) (htau : 0 < tau)
    (S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)))
    (C : ℕ → P.M → W) (hS : IsSolutionOn S) (hterminal : S.base.metric 0 = P.metric)
    (hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ)
    (hscalar : metricScalarAt P.metric P.basepoint ≠ 0)
    (hbase : ∀ n, C n P.basepoint = x (j n))
    (r : ℝ) (hr : 0 < r) (hK : IsCompact (riemannianClosedBallOf P.metric P.basepoint r))
    (hcapture : ∀ᶠ n in atTop,
      riemannianClosedBallOf (scaleMetric (A n) (hA n) gW) (x (j n)) (r / 4) ⊆
        (C n) '' riemannianClosedBallOf P.metric P.basepoint r)
    (hdist : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
      ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
        |metricDistance (scaleMetric (A n) (hA n) gW) (C n a) (C n b) -
          metricDistance P.metric a b| < eta) : False := by
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop,
      Q (j n) * dist (x (j n) : UniformSpace.Completion W) q0 ^ 2 ≤ B := by
    obtain ⟨B, hB⟩ := hupper
    exact ⟨B, hj.tendsto_atTop hB⟩
  obtain ⟨hAtop, B, hcenter⟩ := actual_curvature_scale_bounds (fun n => Q (j n)) A
    (fun n => dist (x (j n) : UniformSpace.Completion W) q0) hA (fun _ => dist_nonneg)
    (hQ.comp hj.tendsto_atTop) hratio hc (hj.tendsto_atTop hlower) hupper'
  exact riemannian_rescaled_cone_solution_exclusion gW hWmetric cone (fun n => x (j n)) A hA hAtop (Real.sqrt (c / 2)) B
    (Real.sqrt_pos.mpr (half_pos hc)) hcenter
    P hpath tau htau S C hS hterminal hsec hscalar hbase r hr hK hcapture hdist

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
