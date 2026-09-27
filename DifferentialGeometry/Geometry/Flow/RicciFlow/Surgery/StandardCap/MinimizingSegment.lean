import DifferentialGeometry.Analysis.Asymptotics.MultiplicativeComparison
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.AmbientSpatialCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Topology.MetricSpace.GeodesicSeparator
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe u

private theorem not_mem_interior_of_minimizing_far_of_subset_ball
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (h : SmoothRiemannianMetric I3 M) {r : ℝ} (hr : 0 < r)
    {K : Set M} {z x : M} (hball : K ⊆ riemannianBallOf h z (2 * r)) (hx : x ∈ K)
    {γ : ℝ → M} {a t b s : ℝ} (ht : t ∈ Icc a b) (hs : s ∈ Icc a b)
    (hmin : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      riemannianEDistOf h (γ u) (γ v) = ENNReal.ofReal |u - v|)
    (hpoint : γ t = x) (hfar : 4 * r ≤ |t - s|) : γ s ∉ interior K := by
  intro hin
  have hm : riemannianEDistOf h x z < ENNReal.ofReal (2 * r) := by
    rw [riemannianEDistOf_comm]
    exact hball hx
  have hy : riemannianEDistOf h z (γ s) < ENNReal.ofReal (2 * r) := hball (interior_subset hin)
  have houter : riemannianEDistOf h x (γ s) < ENNReal.ofReal (4 * r) := by
    apply (riemannianEDistOf_triangle h x z (γ s)).trans_lt
    have heq : ENNReal.ofReal (2 * r) + ENNReal.ofReal (2 * r) = ENNReal.ofReal (4 * r) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    exact (ENNReal.add_lt_add hm hy).trans_eq heq
  rw [← hpoint, hmin t ht s hs] at houter
  exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal hfar)) houter

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem minimizing_endpoint_mem_of_spatial_cap
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (h : SmoothRiemannianMetric I3 M) {r eps : ℝ} (hr : 0 < r)
    {p z x : M} (nk : SpatialNeck h eps p)
    (hscalar : |metricScalarAt h p - 1| ≤ eps)
    {K : Set M} (hfront : frontier K = range (fun q : Sphere 2 => nk.map (q,0)))
    (hball : K ⊆ riemannianBallOf h z (2 * r)) (hx : x ∈ interior K)
    (hxball : riemannianBallOf h x 2000 ⊆ interior K)
    {γ : ℝ → M} {a t b : ℝ} (ht : t ∈ Icc a b)
    (hmin : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      riemannianEDistOf h (γ u) (γ v) = ENNReal.ofReal |u - v|)
    (hpoint : γ t = x) (hleft : 4 * r ≤ t - a) : γ b ∈ interior K := by
  by_contra hb
  have ha : γ a ∉ interior K :=
    not_mem_interior_of_minimizing_far_of_subset_ball h hr hball (interior_subset hx)
      ht ⟨le_rfl, ht.1.trans ht.2⟩ hmin hpoint (by
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
        exact hleft)
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I3
  let _ : RegularSpace M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨h.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (TangentSpace I3 : M → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  have hroot : 9 / 10 < Real.sqrt (metricScalarAt h p) := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 10)).mpr
    have hh := (abs_le.mp hscalar).1
    linarith [nk.eps_small]
  have hepsroot : Real.sqrt (1 + eps) < 11 / 10 := by
    apply (Real.sqrt_lt (by linarith [nk.eps_pos] : 0 ≤ 1 + eps) (by norm_num)).mpr
    linarith [nk.eps_small]
  have hboundary : ∀ y ∈ frontier K, edist p y < ENNReal.ofReal (8 : ℝ) := by
    intro y hy
    obtain ⟨q, rfl⟩ := hfront ▸ hy
    have hh := nk.image_slab_subset_closedBall (r := 0) le_rfl (inv_pos.mpr nk.eps_pos)
      ⟨(q,0), ⟨mem_univ _, by norm_num⟩, rfl⟩
    apply hh.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 8)).mpr
    apply (div_lt_iff₀ (by linarith : 0 < Real.sqrt (metricScalarAt h p))).mpr
    nlinarith
  have hshort : ∀ y ∈ frontier K, ∀ w ∈ frontier K,
      edist y w < ENNReal.ofReal (2000 : ℝ) + ENNReal.ofReal (2000 : ℝ) := by
    intro y hy w hw
    have hh := edist_triangle y p w
    rw [edist_comm y p] at hh
    apply hh.trans_lt
    exact (ENNReal.add_lt_add (hboundary y hy) (hboundary w hw)).trans (by norm_num)
  apply EMetric.not_eball_subset_interior_of_minimizing_of_frontier_edist_lt ht hmin ha hb
    (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 2000)) hshort
  intro y hy
  apply hxball
  change edist x y < ENNReal.ofReal (2000 : ℝ)
  simpa only [hpoint, Metric.mem_eball, edist_comm] using hy

theorem eventually_minimizing_segment_arm_lt_of_metric_cp_convergence
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D)
    (hdepth : 2 * transitionEnd + 2000 < r / 2)
    (N : ℕ) (hN : ⌈eps⁻¹⌉₊ ≤ N)
    (g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D))
    (hconv : MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
      (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)))
    (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
    [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
    (h : ∀ n, SmoothRiemannianMetric I3 (P n))
    (Φ : ∀ n, standardCapWindow D → P n)
    (hΦ : ∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) (hinj : ∀ n, Function.Injective (Φ n))
    (hmetric : ∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
      (g n).inner x v w = (h n).inner (Φ n x)
        (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) :
    ∀ᶠ n in Filter.atTop, ∀ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd →
      ∀ (γ : ℝ → P n) (a t b : ℝ), t ∈ Icc a b →
        (∀ s ∈ Icc a b, ∀ v ∈ Icc a b,
          riemannianEDistOf (h n) (γ s) (γ v) = ENNReal.ofReal |s - v|) →
        γ t = Φ n x → t - a < 4 * r ∨ b - t < 4 * r := by
  have hrpos : 0 < r := by linarith [transitionEnd_pos, inv_pos.mpr heps]
  filter_upwards [eventually_spatial_cap_frontier_with_ball_of_metric_cp_convergence
    D r eps 2000 heps hsmall hr hfit hdepth N hN g hconv P h Φ hΦ hinj hmetric] with n hn
  obtain ⟨p,z,hp,hz,nk,K,hcarrier,hcap,hzero,hmarks,hmap,hfront,hemb,hside,hscalar,hball⟩ := hn
  intro x hx γ a t b ht hmin hpoint
  by_contra! harms
  obtain ⟨hxin, hxscalar, hxball⟩ := hmarks x hx
  have hbin := minimizing_endpoint_mem_of_spatial_cap (h n) hrpos nk hscalar hfront hball
    hxin hxball ht hmin hpoint harms.1
  exact not_mem_interior_of_minimizing_far_of_subset_ball (h n) hrpos hball
    (interior_subset hxin) ht ⟨ht.1.trans ht.2, le_rfl⟩ hmin hpoint (by
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith [harms.2]) hbin

theorem exists_minimizing_segment_left_arm_bound_of_endpoint_scalar_gt
    (D r : ℝ) (hRD : r < D + 1) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
        transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
        2 * transitionEnd + 2000 < r / 2 →
        ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
        ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
        MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
          (metric.restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) →
        ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
          [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
          (h : ∀ n, SmoothRiemannianMetric I3 (P n))
          (Φ : ∀ n, standardCapWindow D → P n),
          (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) →
          (∀ n, Function.Injective (Φ n)) →
          (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
            (g n).inner x v w = (h n).inner (Φ n x)
              (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
          ∀ᶠ n in Filter.atTop, ∀ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd →
            ∀ (γ : ℝ → P n) (a t b : ℝ), t ∈ Icc a b →
              (∀ s ∈ Icc a b, ∀ v ∈ Icc a b,
                riemannianEDistOf (h n) (γ s) (γ v) = ENNReal.ofReal |s - v|) →
              γ t = Φ n x → C < metricScalarAt (h n) (γ b) → t - a < 4 * r := by
  let _ : SigmaCompactSpace (standardCapWindow D) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (standardCapWindow D).isOpen)
  obtain ⟨η, C, hη, hC, hscalar⟩ := exists_uniform_window_scalar_bounds_of_metric_close D r hRD
  refine ⟨C, hC, ?_⟩
  intro eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h Φ hΦ hinj hmetric
  have hrpos : 0 < r := by linarith [transitionEnd_pos, inv_pos.mpr heps]
  have hinv : (11 : ℝ) < eps⁻¹ := by
    have hh := one_div_lt_one_div_of_lt heps hsmall
    norm_num at hh
    exact hh
  have htwo : 2 ≤ N := by
    have hh := (Nat.le_ceil eps⁻¹).trans (Nat.cast_le.mpr hN)
    have hn : (2 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast hn
  have hcompact : IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r + eps⁻¹} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) (r + eps⁻¹)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change ‖x‖ < D + 1
      change ‖x‖ ≤ r + eps⁻¹ at hx
      linarith)
  obtain ⟨n₀, hn₀⟩ := hconv η hη
  filter_upwards [eventually_spatial_cap_frontier_with_ball_of_metric_cp_convergence
    D r eps 2000 heps hsmall hr hfit hdepth N hN g hconv P h Φ hΦ hinj hmetric,
    Filter.eventually_ge_atTop n₀] with n hn hnlarge
  obtain ⟨p,z,hp,hz,nk,K,hcarrier,hcap,hzero,hmarks,hmap,hfront,hemb,hside,hsc,hball⟩ := hn
  have hclose : metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r}
      2 (g n) (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal η := by
    apply (metricDerivENormSupOn_mono (show {x : standardCapWindow D | ‖x.val‖ ≤ r} ⊆
      {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} from
        fun x hx => (show ‖x.val‖ ≤ r from hx).trans (le_add_of_nonneg_right (inv_pos.mpr heps).le)) htwo (g n) _ _).trans_lt
    rw [metricDerivENormSupOn_eq_ofReal_of_isCompact hcompact]
    exact (ENNReal.ofReal_lt_ofReal_iff hη).mpr (hn₀ n hnlarge)
  have hbound : ∀ y ∈ K.carrier, metricScalarAt (h n) y < C := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hcarrier ▸ hy
    have hh := (hscalar (g n) hclose w hw).2
    rwa [(curvature_of_injective_local_isometry (g n) (h n) (Φ n) (hΦ n) (hinj n)
      (hmetric n) w).1] at hh
  intro x hx γ a t b ht hmin hpoint hhigh
  by_contra! hlong
  obtain ⟨hxin, hxscalar, hxball⟩ := hmarks x hx
  have hbin := minimizing_endpoint_mem_of_spatial_cap (h n) hrpos nk hsc hfront hball
    hxin hxball ht hmin hpoint hlong
  exact (hbound (γ b) (interior_subset hbin)).not_gt hhigh

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_uniform_scalar_normalized_minimizing_segment_arm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (D r eps : ℝ), 0 < eps → eps < 1 / 11 →
      transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
      2 * transitionEnd + 2000 < r / 2 →
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ),
      (∀ n, 0 < q n) → ∀ Φ : ∀ n, standardCapWindow D → P n,
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
        (g n).inner x v w = q n * (h n).inner (Φ n x)
          (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
      ∀ᶠ n in Filter.atTop, ∀ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd →
        ∀ (γ : ℝ → P n) (a t b : ℝ), t ∈ Icc a b →
          (∀ s ∈ Icc a b, ∀ v ∈ Icc a b,
            riemannianEDistOf (h n) (γ s) (γ v) = ENNReal.ofReal |s - v|) →
          γ t = Φ n x →
          Real.sqrt (metricScalarAt (h n) (Φ n x)) * (t - a) < 4 * r * Real.sqrt C ∨
          Real.sqrt (metricScalarAt (h n) (Φ n x)) * (b - t) < 4 * r * Real.sqrt C := by
  obtain ⟨C, hC, hcore⟩ := exists_uniform_scalar_bound_on_core_of_metric_cp_convergence
  refine ⟨C, hC, ?_⟩
  intro D r eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj hmetric
  have hD : transitionEnd < D + 1 := by linarith [inv_pos.mpr heps]
  have htwo : 2 ≤ N := by
    have hi : (2 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    exact_mod_cast (hi.trans (Nat.le_ceil eps⁻¹)).trans (Nat.cast_le.mpr hN)
  have hcompact : IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r + eps⁻¹} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) (r + eps⁻¹)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      change ‖x‖ ≤ r + eps⁻¹ at hx
      exact ⟨⟨x, by change ‖x‖ < D + 1; linarith⟩, rfl⟩)
  have hconvCore : MetricCPConvergenceOn
      {x : standardCapWindow D | ‖x.val‖ ≤ transitionEnd} N g
      (metric.restrictOpen (standardCapWindow D)) (metric.restrictOpen (standardCapWindow D)) := by
    intro eta heta
    obtain ⟨n0, hn0⟩ := hconv (eta / 2) (half_pos heta)
    refine ⟨n0, fun n hn => lt_of_le_of_lt
      (metricDerivNormSupOn_le_of_forall _ N _ _ _ (eta / 2) (half_pos heta).le ?_)
      (half_lt_self heta)⟩
    intro j hj x hx
    change ‖x.val‖ ≤ transitionEnd at hx
    exact (derivNorm_le_sup hcompact hj _ _ _ (by
      change ‖x.val‖ ≤ r + eps⁻¹
      linarith [inv_pos.mpr heps])).trans (hn0 n hn).le
  have harmevent := eventually_minimizing_segment_arm_lt_of_metric_cp_convergence
    D r eps heps hsmall hr hfit hdepth N hN g hconv P
    (fun n => scaleMetric (q n) (hq n) (h n)) Φ hΦ hinj hmetric
  filter_upwards [hcore D hD N htwo g hconvCore, harmevent] with n hscalar harm
  intro x hx γ a t b ht hmin hpoint
  have hqroot : 0 < Real.sqrt (q n) := Real.sqrt_pos.mpr (hq n)
  have hpull : g n = localPullMetric (scaleMetric (q n) (hq n) (h n)) (Φ n) (hΦ n) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, scaleMetric_inner]
    exact hmetric n y v w
  have hR : metricScalarAt (h n) (Φ n x) ≤ C * q n := by
    have hh := hscalar x hx
    rw [hpull, metricScalarAt_localPull, metricScalarAt_scaleMetric, ← div_eq_inv_mul] at hh
    exact (div_le_iff₀ (hq n)).mp hh
  have hsqrt : Real.sqrt (metricScalarAt (h n) (Φ n x)) ≤
      Real.sqrt C * Real.sqrt (q n) := by
    rw [← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hR
  let γq : ℝ → P n := fun s => γ (s / Real.sqrt (q n))
  have hinterval {s : ℝ} (hs : s ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b)) :
      s / Real.sqrt (q n) ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hqroot).mpr
      simpa only [mul_comm] using hs.1
    · apply (div_le_iff₀ hqroot).mpr
      simpa only [mul_comm] using hs.2
  have hminq : ∀ s ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b),
      ∀ v ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b),
        riemannianEDistOf (scaleMetric (q n) (hq n) (h n)) (γq s) (γq v) =
          ENNReal.ofReal |s - v| := by
    intro s hs v hv
    rw [edistOf_scale, hmin _ (hinterval hs) _ (hinterval hv),
      ← ENNReal.ofReal_mul hqroot.le]
    congr 1
    rw [← sub_div, abs_div, abs_of_pos hqroot, mul_div_cancel₀ _ hqroot.ne']
  have hmarkq : γq (Real.sqrt (q n) * t) = Φ n x := by
    dsimp only [γq]
    rw [mul_div_cancel_left₀ t hqroot.ne']
    exact hpoint
  have harms := harm x hx γq (Real.sqrt (q n) * a) (Real.sqrt (q n) * t)
    (Real.sqrt (q n) * b)
    ⟨mul_le_mul_of_nonneg_left ht.1 hqroot.le, mul_le_mul_of_nonneg_left ht.2 hqroot.le⟩
    hminq hmarkq
  have hbound (ell : ℝ) (hell : 0 ≤ ell) (harm : Real.sqrt (q n) * ell < 4 * r) :
      Real.sqrt (metricScalarAt (h n) (Φ n x)) * ell < 4 * r * Real.sqrt C := by
    calc
      _ ≤ (Real.sqrt C * Real.sqrt (q n)) * ell := mul_le_mul_of_nonneg_right hsqrt hell
      _ = Real.sqrt C * (Real.sqrt (q n) * ell) := mul_assoc _ _ _
      _ < Real.sqrt C * (4 * r) := mul_lt_mul_of_pos_left harm (Real.sqrt_pos.mpr hC)
      _ = 4 * r * Real.sqrt C := mul_comm _ _
  rcases harms with ha | hb
  · exact Or.inl (hbound (t - a) (sub_nonneg.mpr ht.1) (by rwa [mul_sub]))
  · exact Or.inr (hbound (b - t) (sub_nonneg.mpr ht.2) (by rwa [mul_sub]))


attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_uniform_scalar_normalized_left_arm_bound_of_endpoint_scalar_gt :
    ∃ C : ℝ, 0 < C ∧ ∀ (D r : ℝ), r < D + 1 →
      ∃ Cend : ℝ, 1 ≤ Cend ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
      transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
      2 * transitionEnd + 2000 < r / 2 →
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ),
      (∀ n, 0 < q n) → ∀ Φ : ∀ n, standardCapWindow D → P n,
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
        (g n).inner x v w = q n * (h n).inner (Φ n x)
          (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
      ∀ᶠ n in Filter.atTop, ∀ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd →
        ∀ (γ : ℝ → P n) (a t b : ℝ), t ∈ Icc a b →
          (∀ s ∈ Icc a b, ∀ v ∈ Icc a b,
            riemannianEDistOf (h n) (γ s) (γ v) = ENNReal.ofReal |s - v|) →
          γ t = Φ n x → Cend * q n < metricScalarAt (h n) (γ b) →
          Real.sqrt (metricScalarAt (h n) (Φ n x)) * (t - a) < 4 * r * Real.sqrt C := by
  obtain ⟨C, hC, hcore⟩ := exists_uniform_scalar_bound_on_core_of_metric_cp_convergence
  refine ⟨C, hC, ?_⟩
  intro D r hRD
  obtain ⟨Cend, hCend, hleft⟩ := exists_minimizing_segment_left_arm_bound_of_endpoint_scalar_gt D r hRD
  refine ⟨Cend, hCend, ?_⟩
  intro eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj hmetric
  have hD : transitionEnd < D + 1 := by linarith [inv_pos.mpr heps]
  have htwo : 2 ≤ N := by
    have hi : (2 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    exact_mod_cast (hi.trans (Nat.le_ceil eps⁻¹)).trans (Nat.cast_le.mpr hN)
  have hcompact : IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r + eps⁻¹} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) (r + eps⁻¹)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      change ‖x‖ ≤ r + eps⁻¹ at hx
      exact ⟨⟨x, by change ‖x‖ < D + 1; linarith⟩, rfl⟩)
  have hconvCore : MetricCPConvergenceOn
      {x : standardCapWindow D | ‖x.val‖ ≤ transitionEnd} N g
      (metric.restrictOpen (standardCapWindow D)) (metric.restrictOpen (standardCapWindow D)) := by
    intro eta heta
    obtain ⟨n0, hn0⟩ := hconv (eta / 2) (half_pos heta)
    refine ⟨n0, fun n hn => lt_of_le_of_lt
      (metricDerivNormSupOn_le_of_forall _ N _ _ _ (eta / 2) (half_pos heta).le ?_)
      (half_lt_self heta)⟩
    intro j hj x hx
    change ‖x.val‖ ≤ transitionEnd at hx
    exact (derivNorm_le_sup hcompact hj _ _ _ (by
      change ‖x.val‖ ≤ r + eps⁻¹
      linarith [inv_pos.mpr heps])).trans (hn0 n hn).le
  have harmevent := hleft eps heps hsmall hr hfit hdepth N hN g hconv P
    (fun n => scaleMetric (q n) (hq n) (h n)) Φ hΦ hinj hmetric
  filter_upwards [hcore D hD N htwo g hconvCore, harmevent] with n hscalar harm
  intro x hx γ a t b ht hmin hpoint hhigh
  have hqroot : 0 < Real.sqrt (q n) := Real.sqrt_pos.mpr (hq n)
  have hpull : g n = localPullMetric (scaleMetric (q n) (hq n) (h n)) (Φ n) (hΦ n) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, scaleMetric_inner]
    exact hmetric n y v w
  have hR : metricScalarAt (h n) (Φ n x) ≤ C * q n := by
    have hh := hscalar x hx
    rw [hpull, metricScalarAt_localPull, metricScalarAt_scaleMetric, ← div_eq_inv_mul] at hh
    exact (div_le_iff₀ (hq n)).mp hh
  have hsqrt : Real.sqrt (metricScalarAt (h n) (Φ n x)) ≤
      Real.sqrt C * Real.sqrt (q n) := by
    rw [← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hR
  let γq : ℝ → P n := fun s => γ (s / Real.sqrt (q n))
  have hinterval {s : ℝ} (hs : s ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b)) :
      s / Real.sqrt (q n) ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hqroot).mpr
      simpa only [mul_comm] using hs.1
    · apply (div_le_iff₀ hqroot).mpr
      simpa only [mul_comm] using hs.2
  have hminq : ∀ s ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b),
      ∀ v ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b),
        riemannianEDistOf (scaleMetric (q n) (hq n) (h n)) (γq s) (γq v) =
          ENNReal.ofReal |s - v| := by
    intro s hs v hv
    rw [edistOf_scale, hmin _ (hinterval hs) _ (hinterval hv),
      ← ENNReal.ofReal_mul hqroot.le]
    congr 1
    rw [← sub_div, abs_div, abs_of_pos hqroot, mul_div_cancel₀ _ hqroot.ne']
  have hmarkq : γq (Real.sqrt (q n) * t) = Φ n x := by
    dsimp only [γq]
    rw [mul_div_cancel_left₀ t hqroot.ne']
    exact hpoint
  have hhighq : Cend < metricScalarAt (scaleMetric (q n) (hq n) (h n))
      (γq (Real.sqrt (q n) * b)) := by
    dsimp only [γq]
    rw [mul_div_cancel_left₀ b hqroot.ne', metricScalarAt_scaleMetric, ← div_eq_inv_mul]
    exact (lt_div_iff₀ (hq n)).mpr hhigh
  have harms := harm x hx γq (Real.sqrt (q n) * a) (Real.sqrt (q n) * t)
    (Real.sqrt (q n) * b)
    ⟨mul_le_mul_of_nonneg_left ht.1 hqroot.le, mul_le_mul_of_nonneg_left ht.2 hqroot.le⟩
    hminq hmarkq hhighq
  have hscaled : Real.sqrt (q n) * (t - a) < 4 * r := by
    simpa only [mul_sub] using harms
  calc
    _ ≤ (Real.sqrt C * Real.sqrt (q n)) * (t - a) :=
      mul_le_mul_of_nonneg_right hsqrt (sub_nonneg.mpr ht.1)
    _ = Real.sqrt C * (Real.sqrt (q n) * (t - a)) := mul_assoc _ _ _
    _ < Real.sqrt C * (4 * r) := mul_lt_mul_of_pos_left hscaled (Real.sqrt_pos.mpr hC)
    _ = 4 * r * Real.sqrt C := mul_comm _ _


attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
open Filter in
theorem exists_uniform_scalar_normalized_left_arm_bound_of_endpoint_scalar_tendsto_atTop :
    ∃ C : ℝ, 0 < C ∧ ∀ (D r eps : ℝ), 0 < eps → eps < 1 / 11 →
      transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
      2 * transitionEnd + 2000 < r / 2 →
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ),
      (∀ n, 0 < q n) → ∀ Φ : ∀ n, standardCapWindow D → P n,
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
        (g n).inner x v w = q n * (h n).inner (Φ n x)
          (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
      ∀ u : ℕ → standardCapWindow D, (∀ᶠ n in atTop, ‖(u n).val‖ ≤ transitionEnd) →
      ∀ (γ : ∀ n, ℝ → P n) (ell : ℕ → ℝ) (rho t R : ℝ),
      Tendsto ell atTop (𝓝 rho) → t ∈ Ico 0 rho →
      (∀ᶠ n in atTop, ∀ s ∈ Icc 0 (ell n), ∀ v ∈ Icc 0 (ell n),
        riemannianEDistOf (h n) (γ n s) (γ n v) = ENNReal.ofReal |s - v|) →
      (∀ᶠ n in atTop, γ n t = Φ n (u n)) →
      Tendsto (fun n => metricScalarAt (h n) (γ n t)) atTop (𝓝 R) →
      Tendsto (fun n => metricScalarAt (h n) (γ n (ell n))) atTop atTop →
      Real.sqrt R * t ≤ 4 * r * Real.sqrt C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_scalar_normalized_left_arm_bound_of_endpoint_scalar_gt
  refine ⟨C, hC, ?_⟩
  intro D r eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj
    hmetric u hu γ ell rho t R hell ht hmin hpoint hR hend
  have hRD : r < D + 1 := by linarith [inv_pos.mpr heps]
  obtain ⟨Cend, hCend, hleft⟩ := hbound D r hRD
  have htwo : 2 ≤ N := by
    have hi : (2 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    exact_mod_cast (hi.trans (Nat.le_ceil eps⁻¹)).trans (Nat.cast_le.mpr hN)
  have hhalf := eventually_half_lt_metricScalarAt_of_metric_cp_convergence
    (show r + eps⁻¹ < D + 1 by linarith) htwo g hconv
  have hqm : ∀ᶠ n in atTop, (1 / 2 : ℝ) * q n ≤ metricScalarAt (h n) (γ n t) := by
    filter_upwards [hhalf, hu, hpoint] with n hn hun hpn
    have hh := hn (u n) (show ‖(u n).val‖ ≤ r + eps⁻¹ by linarith [inv_pos.mpr heps])
    have hpull : g n = localPullMetric (scaleMetric (q n) (hq n) (h n)) (Φ n) (hΦ n) := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [localPullMetric_inner, scaleMetric_inner]
      exact hmetric n x v w
    rw [hpull, metricScalarAt_localPull, metricScalarAt_scaleMetric, ← div_eq_inv_mul] at hh
    rw [hpn]
    exact (le_div_iff₀ (hq n)).mp hh.le
  have hratio : Tendsto (fun n => metricScalarAt (h n) (γ n (ell n)) / q n) atTop atTop :=
    DifferentialGeometry.Analysis.tendsto_div_atTop_of_tendsto_div_nhds_of_mul_le
      (b := fun _ => (1 : ℝ)) (c := (1 / 2 : ℝ)) (by norm_num)
      (Eventually.of_forall fun _ => zero_lt_one) (Eventually.of_forall hq)
      (by simpa only [div_one] using hR) hqm (by simpa only [div_one] using hend)
  have hevent := hleft eps heps hsmall hr hfit hdepth N hN g hconv P h q hq Φ hΦ hinj hmetric
  have hlength : ∀ᶠ n in atTop, t < ell n := hell.eventually (Ioi_mem_nhds ht.2)
  have hlim : Tendsto (fun n => Real.sqrt (metricScalarAt (h n) (γ n t)) * t) atTop
      (𝓝 (Real.sqrt R * t)) := (Real.continuous_sqrt.tendsto R |>.comp hR).mul_const t
  apply le_of_tendsto hlim
  filter_upwards [hevent, hu, hmin, hpoint, hlength, hratio.eventually_gt_atTop Cend]
    with n hn hun hmn hpn htn hhigh
  have hh := hn (u n) hun (γ n) 0 t (ell n) ⟨ht.1, htn.le⟩ hmn hpn
    ((lt_div_iff₀ (hq n)).mp hhigh)
  rw [← hpn, sub_zero] at hh
  exact hh.le


attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
open Filter in
theorem eventually_minimizing_segment_cap_window_exclusion_of_scalar_blowup
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D)
    (hdepth : 2 * transitionEnd + 2000 < r / 2)
    (rho : ℝ) (hrho : 0 < rho) (R : Ico 0 rho → ℝ)
    (hR : Tendsto R (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop) :
    ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ),
      (∀ n, 0 < q n) → ∀ Φ : ∀ n, standardCapWindow D → P n,
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
        (g n).inner x v w = q n * (h n).inner (Φ n x)
          (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
      ∀ u : ℕ → standardCapWindow D, (∀ᶠ n in atTop, ‖(u n).val‖ ≤ transitionEnd) →
      ∀ (γ : ∀ n, ℝ → P n) (ell : ℕ → ℝ),
      Tendsto ell atTop (𝓝 rho) →
      (∀ᶠ n in atTop, ∀ s ∈ Icc 0 (ell n), ∀ v ∈ Icc 0 (ell n),
        riemannianEDistOf (h n) (γ n s) (γ n v) = ENNReal.ofReal |s - v|) →
      (∀ᶠ n in atTop, γ n t = Φ n (u n)) →
      Tendsto (fun n => metricScalarAt (h n) (γ n t)) atTop (𝓝 (R t)) →
      Tendsto (fun n => metricScalarAt (h n) (γ n (ell n))) atTop atTop → False := by
  obtain ⟨C, _, hbound⟩ :=
    exists_uniform_scalar_normalized_left_arm_bound_of_endpoint_scalar_tendsto_atTop
  have hlarge : Tendsto (fun t : Ico 0 rho => Real.sqrt (R t) * (t : ℝ))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop :=
    (Real.tendsto_sqrt_atTop.comp hR).atTop_mul_pos hrho tendsto_comap
  filter_upwards [hlarge.eventually_gt_atTop (4 * r * Real.sqrt C)] with t ht
  intro N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj hmetric u hu γ ell hell hmin hpoint hmark hend
  exact ht.not_ge (hbound D r eps heps hsmall hr hfit hdepth N hN g hconv P h q hq Φ hΦ hinj
    hmetric u hu γ ell rho t (R t) hell t.property hmin hpoint hmark hend)

theorem exists_minimizing_segment_left_arm_bound_near_core_of_endpoint_scalar_gt
    (D r : ℝ) (hRD : r < D + 1) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
        transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
        2 * transitionEnd + 4000 < r / 2 →
        ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
        ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
        MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
          (metric.restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) →
        ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
          [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
          (h : ∀ n, SmoothRiemannianMetric I3 (P n))
          (Φ : ∀ n, standardCapWindow D → P n),
          (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) →
          (∀ n, Function.Injective (Φ n)) →
          (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
            (g n).inner x v w = (h n).inner (Φ n x)
              (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
          ∀ᶠ n in Filter.atTop, ∀ u : standardCapWindow D, ‖u.val‖ ≤ transitionEnd →
            ∀ x : P n, riemannianEDistOf (h n) x (Φ n u) ≤ ENNReal.ofReal (4 : ℝ) →
            (1 / 2 < metricScalarAt (h n) x ∧ metricScalarAt (h n) x < C) ∧
            ∀ (γ : ℝ → P n) (a t b : ℝ), t ∈ Icc a b →
              (∀ s ∈ Icc a b, ∀ v ∈ Icc a b,
                riemannianEDistOf (h n) (γ s) (γ v) = ENNReal.ofReal |s - v|) →
              γ t = x → C < metricScalarAt (h n) (γ b) → t - a < 4 * r := by
  let _ : SigmaCompactSpace (standardCapWindow D) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (standardCapWindow D).isOpen)
  obtain ⟨η, C, hη, hC, hscalar⟩ := exists_uniform_window_scalar_bounds_of_metric_close D r hRD
  refine ⟨C, hC, ?_⟩
  intro eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h Φ hΦ hinj hmetric
  have hrpos : 0 < r := by linarith [transitionEnd_pos, inv_pos.mpr heps]
  have hinv : (11 : ℝ) < eps⁻¹ := by
    have hh := one_div_lt_one_div_of_lt heps hsmall
    norm_num at hh
    exact hh
  have htwo : 2 ≤ N := by
    have hh := (Nat.le_ceil eps⁻¹).trans (Nat.cast_le.mpr hN)
    have hn : (2 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast hn
  have hcompact : IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r + eps⁻¹} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) (r + eps⁻¹)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change ‖x‖ < D + 1
      change ‖x‖ ≤ r + eps⁻¹ at hx
      linarith)
  obtain ⟨n₀, hn₀⟩ := hconv η hη
  filter_upwards [eventually_spatial_cap_frontier_with_ball_of_metric_cp_convergence
    D r eps 4000 heps hsmall hr hfit hdepth N hN g hconv P h Φ hΦ hinj hmetric,
    Filter.eventually_ge_atTop n₀] with n hn hnlarge
  obtain ⟨p,z,hp,hz,nk,K,hcarrier,hcap,hzero,hmarks,hmap,hfront,hemb,hside,hsc,hball⟩ := hn
  have hclose : metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r}
      2 (g n) (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal η := by
    apply (metricDerivENormSupOn_mono (show {x : standardCapWindow D | ‖x.val‖ ≤ r} ⊆
      {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} from
        fun x hx => (show ‖x.val‖ ≤ r from hx).trans (le_add_of_nonneg_right (inv_pos.mpr heps).le)) htwo (g n) _ _).trans_lt
    rw [metricDerivENormSupOn_eq_ofReal_of_isCompact hcompact]
    exact (ENNReal.ofReal_lt_ofReal_iff hη).mpr (hn₀ n hnlarge)
  have hbound : ∀ y ∈ K.carrier,
      1 / 2 < metricScalarAt (h n) y ∧ metricScalarAt (h n) y < C := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hcarrier ▸ hy
    have hh := hscalar (g n) hclose w hw
    rwa [(curvature_of_injective_local_isometry (g n) (h n) (Φ n) (hΦ n) (hinj n)
      (hmetric n) w).1] at hh
  intro u hu x hx
  obtain ⟨huin, huscalar, huball⟩ := hmarks u hu
  have hxball : riemannianBallOf (h n) x 2000 ⊆ interior K.carrier := by
    intro y hy
    apply huball
    change riemannianEDistOf (h n) (Φ n u) y < ENNReal.ofReal (4000 : ℝ)
    have hux : riemannianEDistOf (h n) (Φ n u) x ≤ ENNReal.ofReal (4 : ℝ) := by
      rwa [riemannianEDistOf_comm] at hx
    have hh := (riemannianEDistOf_triangle (h n) (Φ n u) x y).trans
      (add_le_add hux (show riemannianEDistOf (h n) x y ≤ ENNReal.ofReal (2000 : ℝ) from hy.le))
    exact hh.trans_lt (by norm_num)
  have hxin : x ∈ interior K.carrier := hxball (by
    change riemannianEDistOf (h n) x x < ENNReal.ofReal (2000 : ℝ)
    rw [riemannianEDistOf_self]
    norm_num)
  refine ⟨hbound x (interior_subset hxin), ?_⟩
  intro γ a t b ht hmin hpoint hhigh
  by_contra! hlong
  have hbin := minimizing_endpoint_mem_of_spatial_cap (h n) hrpos nk hsc hfront hball
    hxin hxball ht hmin hpoint hlong
  exact (hbound (γ b) (interior_subset hbin)).2.not_gt hhigh

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_scalar_normalized_left_arm_bound_near_core_of_endpoint_scalar_gt
    (D r : ℝ) (hRD : r < D + 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
      transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
      2 * transitionEnd + 4000 < r / 2 →
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ),
      ∀ hq : (∀ n, 0 < q n), ∀ Φ : ∀ n, standardCapWindow D → P n,
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
        (g n).inner x v w = q n * (h n).inner (Φ n x)
          (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
      ∀ᶠ n in Filter.atTop, ∀ u : standardCapWindow D, ‖u.val‖ ≤ transitionEnd →
        ∀ x : P n, riemannianEDistOf (scaleMetric (q n) (hq n) (h n)) x (Φ n u) ≤ ENNReal.ofReal (4 : ℝ) →
        ((1 / 2 : ℝ) * q n < metricScalarAt (h n) x ∧ metricScalarAt (h n) x < C * q n) ∧
        ∀ (γ : ℝ → P n) (a t b : ℝ), t ∈ Icc a b →
          (∀ s ∈ Icc a b, ∀ v ∈ Icc a b,
            riemannianEDistOf (h n) (γ s) (γ v) = ENNReal.ofReal |s - v|) →
          γ t = x → C * q n < metricScalarAt (h n) (γ b) →
          Real.sqrt (metricScalarAt (h n) x) * (t - a) < 4 * r * Real.sqrt C := by
  obtain ⟨C, hC, hleft⟩ := exists_minimizing_segment_left_arm_bound_near_core_of_endpoint_scalar_gt D r hRD
  refine ⟨C, hC, ?_⟩
  intro eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj hmetric
  have harmevent := hleft eps heps hsmall hr hfit hdepth N hN g hconv P
    (fun n => scaleMetric (q n) (hq n) (h n)) Φ hΦ hinj hmetric
  filter_upwards [harmevent] with n hn
  intro u hu x hx
  have harm := hn u hu x hx
  have hscalar : (1 / 2 : ℝ) * q n < metricScalarAt (h n) x ∧ metricScalarAt (h n) x < C * q n := by
    have hs := harm.1
    rw [metricScalarAt_scaleMetric, ← div_eq_inv_mul] at hs
    exact ⟨(lt_div_iff₀ (hq n)).mp hs.1, (div_lt_iff₀ (hq n)).mp hs.2⟩
  refine ⟨hscalar, ?_⟩
  intro γ a t b ht hmin hpoint hhigh
  have hqroot : 0 < Real.sqrt (q n) := Real.sqrt_pos.mpr (hq n)
  have hsqrt : Real.sqrt (metricScalarAt (h n) x) ≤
      Real.sqrt C * Real.sqrt (q n) := by
    rw [← Real.sqrt_mul (zero_le_one.trans hC)]
    exact Real.sqrt_le_sqrt hscalar.2.le
  let γq : ℝ → P n := fun s => γ (s / Real.sqrt (q n))
  have hinterval {s : ℝ} (hs : s ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b)) :
      s / Real.sqrt (q n) ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hqroot).mpr
      simpa only [mul_comm] using hs.1
    · apply (div_le_iff₀ hqroot).mpr
      simpa only [mul_comm] using hs.2
  have hminq : ∀ s ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b),
      ∀ v ∈ Icc (Real.sqrt (q n) * a) (Real.sqrt (q n) * b),
        riemannianEDistOf (scaleMetric (q n) (hq n) (h n)) (γq s) (γq v) =
          ENNReal.ofReal |s - v| := by
    intro s hs v hv
    rw [edistOf_scale, hmin _ (hinterval hs) _ (hinterval hv),
      ← ENNReal.ofReal_mul hqroot.le]
    congr 1
    rw [← sub_div, abs_div, abs_of_pos hqroot, mul_div_cancel₀ _ hqroot.ne']
  have hmarkq : γq (Real.sqrt (q n) * t) = x := by
    dsimp only [γq]
    rw [mul_div_cancel_left₀ t hqroot.ne']
    exact hpoint
  have hhighq : C < metricScalarAt (scaleMetric (q n) (hq n) (h n))
      (γq (Real.sqrt (q n) * b)) := by
    dsimp only [γq]
    rw [mul_div_cancel_left₀ b hqroot.ne', metricScalarAt_scaleMetric, ← div_eq_inv_mul]
    exact (lt_div_iff₀ (hq n)).mpr hhigh
  have harms := harm.2 γq (Real.sqrt (q n) * a) (Real.sqrt (q n) * t)
    (Real.sqrt (q n) * b)
    ⟨mul_le_mul_of_nonneg_left ht.1 hqroot.le, mul_le_mul_of_nonneg_left ht.2 hqroot.le⟩
    hminq hmarkq hhighq
  have hscaled : Real.sqrt (q n) * (t - a) < 4 * r := by
    simpa only [mul_sub] using harms
  calc
    _ ≤ (Real.sqrt C * Real.sqrt (q n)) * (t - a) :=
      mul_le_mul_of_nonneg_right hsqrt (sub_nonneg.mpr ht.1)
    _ = Real.sqrt C * (Real.sqrt (q n) * (t - a)) := mul_assoc _ _ _
    _ < Real.sqrt C * (4 * r) := mul_lt_mul_of_pos_left hscaled (Real.sqrt_pos.mpr (zero_lt_one.trans_le hC))
    _ = 4 * r * Real.sqrt C := mul_comm _ _

private theorem scaled_edist_lt_four_of_mem_half_ball
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (h : SmoothRiemannianMetric I3 M) {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hscale : q < 4 * (16 / r ^ 2)) {x y : M}
    (hy : y ∈ riemannianClosedBallOf h x (r / 2)) :
    riemannianEDistOf (scaleMetric q hq h) x y < ENNReal.ofReal 4 := by
  have hqr : q * r ^ 2 < 64 := by
    have hqdiv : q < 64 / r ^ 2 := by
      convert hscale using 1
      ring
    exact (lt_div_iff₀ (sq_pos_of_pos hr)).mp hqdiv
  have hproduct : (Real.sqrt q * r) ^ 2 < 8 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq.le]
    norm_num only [Nat.reducePow]
    exact hqr
  have hroot : Real.sqrt q * (r / 2) < 4 := by
    have hnonneg := mul_nonneg (Real.sqrt_nonneg q) hr.le
    nlinarith
  rw [edistOf_scale]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt q) * ENNReal.ofReal (r / 2) :=
      mul_le_mul' le_rfl hy
    _ = ENNReal.ofReal (Real.sqrt q * (r / 2)) :=
      (ENNReal.ofReal_mul (Real.sqrt_nonneg q)).symm
    _ < ENNReal.ofReal 4 :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)).mpr hroot


attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_scalar_normalized_left_arm_bound_of_cap_scale_radius_bound
    (D r : ℝ) (hRD : r < D + 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
      transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
      2 * transitionEnd + 4000 < r / 2 →
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ),
      (∀ n, 0 < q n) → ∀ Φ : ∀ n, standardCapWindow D → P n,
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
        (g n).inner x v w = q n * (h n).inner (Φ n x)
          (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) →
      ∀ᶠ n in Filter.atTop, ∀ u : standardCapWindow D, ‖u.val‖ ≤ transitionEnd →
        ∀ (x : P n) (radius : ℝ), 0 < radius → q n < 4 * (16 / radius ^ 2) →
        Φ n u ∈ riemannianClosedBallOf (h n) x (radius / 2) →
        ((1 / 2 : ℝ) * q n < metricScalarAt (h n) x ∧ metricScalarAt (h n) x < C * q n) ∧
        ∀ (γ : ℝ → P n) (a t b : ℝ), t ∈ Icc a b →
          (∀ s ∈ Icc a b, ∀ v ∈ Icc a b,
            riemannianEDistOf (h n) (γ s) (γ v) = ENNReal.ofReal |s - v|) →
          γ t = x → C * q n < metricScalarAt (h n) (γ b) →
          Real.sqrt (metricScalarAt (h n) x) * (t - a) < 4 * r * Real.sqrt C := by
  obtain ⟨C, hC, hbound⟩ := exists_scalar_normalized_left_arm_bound_near_core_of_endpoint_scalar_gt D r hRD
  refine ⟨C, hC, ?_⟩
  intro eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj hmetric
  filter_upwards [hbound eps heps hsmall hr hfit hdepth N hN g hconv P h q hq Φ hΦ hinj hmetric]
    with n hn
  intro u hu x radius hrad hscale hdist
  exact hn u hu x (scaled_edist_lt_four_of_mem_half_ball (h n) hrad (hq n) hscale hdist).le

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
open Filter in
theorem exists_scalar_normalized_left_arm_bound_near_core_of_endpoint_scalar_tendsto_atTop
    (D r : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 11 →
      transitionEnd + eps⁻¹ + 1 < r → r + eps⁻¹ + 1 ≤ D →
      2 * transitionEnd + 4000 < r / 2 →
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ)
        (hq : ∀ n, 0 < q n) (Φ : ∀ n, standardCapWindow D → P n),
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (z : standardCapWindow D) (v w : TangentSpace I3 z),
        (g n).inner z v w = q n * (h n).inner (Φ n z)
          (mfderiv I3 I3 (Φ n) z v) (mfderiv I3 I3 (Φ n) z w)) →
      ∀ u : ℕ → standardCapWindow D, (∀ᶠ n in atTop, ‖(u n).val‖ ≤ transitionEnd) →
      ∀ x : ∀ n, P n,
      (∀ᶠ n in atTop, riemannianEDistOf (scaleMetric (q n) (hq n) (h n))
        (x n) (Φ n (u n)) ≤ ENNReal.ofReal 4) →
      ∀ (γ : ∀ n, ℝ → P n) (ell : ℕ → ℝ) (rho t R : ℝ),
      Tendsto ell atTop (𝓝 rho) → t ∈ Ico 0 rho →
      (∀ᶠ n in atTop, ∀ s ∈ Icc 0 (ell n), ∀ v ∈ Icc 0 (ell n),
        riemannianEDistOf (h n) (γ n s) (γ n v) = ENNReal.ofReal |s - v|) →
      (∀ᶠ n in atTop, γ n t = x n) →
      Tendsto (fun n => metricScalarAt (h n) (x n)) atTop (𝓝 R) →
      Tendsto (fun n => metricScalarAt (h n) (γ n (ell n))) atTop atTop →
      Real.sqrt R * t ≤ 4 * r * Real.sqrt C := by
  by_cases hRD : r < D + 1
  · obtain ⟨C, hC, hbound⟩ :=
      exists_scalar_normalized_left_arm_bound_near_core_of_endpoint_scalar_gt D r hRD
    refine ⟨C, hC, ?_⟩
    intro eps heps hsmall hr hfit hdepth N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj
      hmetric u hu x hnear γ ell rho t R hell ht hmin hpoint hR hend
    have hevent := hbound eps heps hsmall hr hfit hdepth N hN g hconv P h q hq Φ hΦ hinj hmetric
    have hqm : ∀ᶠ n in atTop, (1 / 2 : ℝ) * q n ≤ metricScalarAt (h n) (x n) := by
      filter_upwards [hevent, hu, hnear] with n hn hun hxn
      exact (hn (u n) hun (x n) hxn).1.1.le
    have hratio : Tendsto (fun n => metricScalarAt (h n) (γ n (ell n)) / q n) atTop atTop :=
      DifferentialGeometry.Analysis.tendsto_div_atTop_of_tendsto_div_nhds_of_mul_le
        (b := fun _ => (1 : ℝ)) (c := (1 / 2 : ℝ)) (by norm_num)
        (Eventually.of_forall fun _ => zero_lt_one) (Eventually.of_forall hq)
        (by simpa only [div_one] using hR) hqm (by simpa only [div_one] using hend)
    have hlength : ∀ᶠ n in atTop, t < ell n := hell.eventually (Ioi_mem_nhds ht.2)
    have hlim : Tendsto (fun n => Real.sqrt (metricScalarAt (h n) (x n)) * t) atTop
        (𝓝 (Real.sqrt R * t)) := (Real.continuous_sqrt.tendsto R |>.comp hR).mul_const t
    apply le_of_tendsto hlim
    filter_upwards [hevent, hu, hnear, hmin, hpoint, hlength, hratio.eventually_gt_atTop C]
      with n hn hun hxn hmn hpn htn hhigh
    have hh := (hn (u n) hun (x n) hxn).2 (γ n) 0 t (ell n) ⟨ht.1, htn.le⟩ hmn hpn
      ((lt_div_iff₀ (hq n)).mp hhigh)
    simpa only [sub_zero] using hh.le
  · refine ⟨1, le_rfl, ?_⟩
    intro eps heps hsmall hr hfit
    exact (hRD (by linarith [inv_pos.mpr heps])).elim

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
open Filter in
theorem eventually_minimizing_segment_near_cap_core_exclusion_of_scalar_blowup
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D)
    (hdepth : 2 * transitionEnd + 4000 < r / 2)
    (rho : ℝ) (hrho : 0 < rho) (R : Ico 0 rho → ℝ)
    (hR : Tendsto R (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop) :
    ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
      ∀ N : ℕ, ⌈eps⁻¹⌉₊ ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r + eps⁻¹} N g
        (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) →
      ∀ (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
        [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
        (h : ∀ n, SmoothRiemannianMetric I3 (P n)) (q : ℕ → ℝ)
        (hq : ∀ n, 0 < q n) (Φ : ∀ n, standardCapWindow D → P n),
      (∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) → (∀ n, Function.Injective (Φ n)) →
      (∀ n (z : standardCapWindow D) (v w : TangentSpace I3 z),
        (g n).inner z v w = q n * (h n).inner (Φ n z)
          (mfderiv I3 I3 (Φ n) z v) (mfderiv I3 I3 (Φ n) z w)) →
      ∀ u : ℕ → standardCapWindow D, (∀ᶠ n in atTop, ‖(u n).val‖ ≤ transitionEnd) →
      ∀ x : ∀ n, P n,
      (∀ᶠ n in atTop, riemannianEDistOf (scaleMetric (q n) (hq n) (h n))
        (x n) (Φ n (u n)) ≤ ENNReal.ofReal 4) →
      ∀ (γ : ∀ n, ℝ → P n) (ell : ℕ → ℝ),
      Tendsto ell atTop (𝓝 rho) →
      (∀ᶠ n in atTop, ∀ s ∈ Icc 0 (ell n), ∀ v ∈ Icc 0 (ell n),
        riemannianEDistOf (h n) (γ n s) (γ n v) = ENNReal.ofReal |s - v|) →
      (∀ᶠ n in atTop, γ n t = x n) →
      Tendsto (fun n => metricScalarAt (h n) (x n)) atTop (𝓝 (R t)) →
      Tendsto (fun n => metricScalarAt (h n) (γ n (ell n))) atTop atTop → False := by
  obtain ⟨C, _, hbound⟩ :=
    exists_scalar_normalized_left_arm_bound_near_core_of_endpoint_scalar_tendsto_atTop D r
  have hlarge : Tendsto (fun t : Ico 0 rho => Real.sqrt (R t) * (t : ℝ))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop :=
    (Real.tendsto_sqrt_atTop.comp hR).atTop_mul_pos hrho tendsto_comap
  filter_upwards [hlarge.eventually_gt_atTop (4 * r * Real.sqrt C)] with t ht
  intro N hN g hconv P _ _ _ _ h q hq Φ hΦ hinj hmetric u hu x hnear γ ell hell hmin hpoint hmark hend
  exact ht.not_ge (hbound eps heps hsmall hr hfit hdepth N hN g hconv P h q hq Φ hΦ hinj
    hmetric u hu x hnear γ ell rho t (R t) hell t.property hmin hpoint hmark hend)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
