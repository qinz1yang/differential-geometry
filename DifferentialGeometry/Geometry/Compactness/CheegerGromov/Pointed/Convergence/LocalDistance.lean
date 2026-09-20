import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Comparison.MetricDistanceTransfer
import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u v uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {N : ℕ → Type v} [∀ k, TopologicalSpace (N k)] [∀ k, ChartedSpace H (N k)]
  [∀ k, IsManifold I ∞ (N k)] [∀ k, T2Space (N k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_isCompact_closedBall_subset_open
    (g : SmoothRiemannianMetric I M) (V : TopologicalSpace.Opens M)
    {q : M} (hq : q ∈ V) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (riemannianClosedBallOf g q R) ∧
      riemannianClosedBallOf g q R ⊆ V := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : RegularSpace M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  obtain ⟨K, hK, hqK, hKV⟩ := exists_compact_subset V.isOpen hq
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds I
    (mem_interior_iff_mem_nhds.mp hqK)
  have hcR : (0 : ℝ) < (c : ℝ) := hc
  have hsub : riemannianClosedBallOf g q ((c : ℝ) / 2) ⊆ K := by
    intro y hy
    apply hball
    change riemannianEDistOf g q y < (c : ℝ≥0∞)
    exact hy.trans_lt (by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.2 (by linarith))
  refine ⟨(c : ℝ) / 2, by positivity, hK.of_isClosed_subset ?_ hsub, hsub.trans hKV⟩
  exact isClosed_le (Geometry.Riemannian.continuous_riemannianEDist g q) continuous_const

omit [SigmaCompactSpace M] [∀ k, T2Space (N k)] in
private theorem eventually_pullback_metric_quadratic_bounds
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (h : ∀ k, SmoothRiemannianMetric I (N k))
    (F : ∀ k, PartialDiffeomorph I I M (N k) ∞)
    (G : ℕ → SmoothRiemannianMetric I U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I x),
      (G k).inner x v w = (h k).inner (F k x)
        (mfderiv I I (F k) x v) (mfderiv I I (F k) x w))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - eps) * g.inner x v v ≤
        (h k).inner (F k x) (mfderiv I I (F k) x v) (mfderiv I I (F k) x v) ∧
      (h k).inner (F k x) (mfderiv I I (F k) x v) (mfderiv I I (F k) x v) ≤
        (1 + eps) * g.inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let KU : Set U := Subtype.val ⁻¹' K
  have hKUcompact : IsCompact KU := by
    apply (Topology.IsEmbedding.subtypeVal.isCompact_iff).2
    have heq : (Subtype.val : U → M) '' KU = K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hKU hx⟩, hx, rfl⟩
    rw [heq]
    exact hK
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨k0, hk0⟩ := hG KU hKUcompact 0 (eps / (n + 1)) (by positivity)
  filter_upwards [eventually_ge_atTop k0, hmetric] with k hk hmet
  intro x hx v
  let xu : U := ⟨x, hKU hx⟩
  have hnorm : metricDerivNorm 0 (G k) (g.restrictOpen U) (g.restrictOpen U) xu ≤
      eps / (n + 1) :=
    (derivNorm_le_sup hKUcompact le_rfl _ _ _ hx).trans (hk0 k hk).le
  have hquad := metricQuadFormDiff_le_metricDerivNorm (G k) (g.restrictOpen U)
    (g.restrictOpen U) xu v
  have hbound : |(G k).inner xu v v - g.inner x v v| ≤ eps * g.inner x v v := by
    have hv : 0 ≤ g.inner x v v := _root_.DifferentialGeometry.metric_inner_self_nonneg g x v
    have hcoeff : n * (eps / (n + 1)) ≤ eps := by
      have heq := div_mul_cancel₀ eps (by positivity : n + 1 ≠ 0)
      nlinarith [div_nonneg heps.le (by positivity : 0 ≤ n + 1)]
    exact hquad.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm hn) hv).trans
      (mul_le_mul_of_nonneg_right hcoeff hv))
  rw [hmet xu v v] at hbound
  have hb := abs_le.mp hbound
  constructor <;> linarith

theorem exists_uniform_local_distance_convergence_and_inverse_capture
    (g : SmoothRiemannianMetric I M) (V U : TopologicalSpace.Opens M)
    (hVU : V ≤ U) (q : M) (hq : q ∈ V)
    (h : ∀ k, SmoothRiemannianMetric I (N k))
    (F : ∀ k, PartialDiffeomorph I I M (N k) ∞)
    (G : ℕ → SmoothRiemannianMetric I U)
    (hG : MetricCInfConvergenceOnCompacts G (g.restrictOpen U) (g.restrictOpen U))
    (hsource : ∀ᶠ k in atTop, (U : Set M) ⊆ (F k).source)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I x),
      (G k).inner x v w = (h k).inner (F k x)
        (mfderiv I I (F k) x v) (mfderiv I I (F k) x w)) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (riemannianClosedBallOf g q R) ∧
      riemannianClosedBallOf g q R ⊆ V ∧
      let K := riemannianClosedBallOf g q (R / 16)
      IsCompact K ∧ K ⊆ V ∧
      (∀ x y : V, (x : M) ∈ K → (y : M) ∈ K →
        riemannianEDistOf (g.restrictOpen V) x y = riemannianEDistOf g x y) ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ k in atTop,
        ∀ a ∈ K, ∀ b ∈ K,
          |(riemannianEDistOf (h k) (F k a) (F k b)).toReal -
            (riemannianEDistOf g a b).toReal| < epsilon) ∧
      ∀ᶠ k in atTop, K ⊆ (F k).source ∧
        ∀ y ∈ riemannianClosedBallOf (h k) (F k q) (R / 64),
          y ∈ (F k).target ∧ (F k).symm y ∈ K ∧ F k ((F k).symm y) = y := by
  obtain ⟨R, hR, hRcompact, hRV⟩ := exists_isCompact_closedBall_subset_open g V hq
  let K := riemannianClosedBallOf g q (R / 16)
  have hKR : K ⊆ riemannianClosedBallOf g q R :=
    riemannianClosedBallOf_mono g q (by linarith)
  have hKcompact : IsCompact K := hRcompact.of_isClosed_subset
    (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist g q) continuous_const) hKR
  have hRU : riemannianClosedBallOf g q R ⊆ U := hRV.trans hVU
  have hrestricted : ∀ x y : V, (x : M) ∈ K → (y : M) ∈ K →
      riemannianEDistOf (g.restrictOpen V) x y = riemannianEDistOf g x y := by
    intro x y hx hy
    let cR : ℝ≥0 := ⟨R, hR.le⟩
    have hball : {z | riemannianEDistOf g q z < (cR : ℝ≥0∞)} ⊆ V := by
      intro z hz
      apply hRV
      have hc : (cR : ℝ≥0∞) = ENNReal.ofReal R := by
        exact (show ENNReal.ofReal (cR : ℝ) = (cR : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal).symm
      exact (hz.trans_eq hc).le
    have hsmall (z : M) (hz : z ∈ K) :
        riemannianEDistOf g q z < ((cR / 3 : ℝ≥0) : ℝ≥0∞) := by
      have hc : ((cR / 3 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (R / 3) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        rfl
      rw [hc]
      exact hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
    exact Geometry.Metric.riemannianEDistOf_restrictOpen_eq_of_ball_subset g V q cR
      hball x y (hsmall x hx) (hsmall y hy)
  refine ⟨R, hR, hRcompact, hRV, hKcompact, hKR.trans hRV, hrestricted, ?_, ?_⟩
  · intro epsilon hepsilon
    let delta : ℝ := min (1 / 4) (epsilon / (2 * (R + 1)))
    have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
    have hdelta4 : delta ≤ 1 / 4 := min_le_left _ _
    have hdeltasmall : delta * (R + 1) < epsilon := by
      have hm := (le_div_iff₀ (by positivity : 0 < 2 * (R + 1))).mp
        (min_le_right (1 / 4 : ℝ) (epsilon / (2 * (R + 1))))
      change delta * (2 * (R + 1)) ≤ epsilon at hm
      nlinarith
    have hquad := eventually_pullback_metric_quadratic_bounds g U h F G hG hmetric
      hRcompact hRU hdelta
    filter_upwards [hquad, hsource] with k hk hsrc
    have hsquarePlus : Real.sqrt (1 + delta) ^ 2 = 1 + delta :=
      Real.sq_sqrt (by linarith)
    have hsquareMinus : Real.sqrt (1 - delta) ^ 2 = 1 - delta :=
      Real.sq_sqrt (by linarith)
    have hplus : Real.sqrt (1 + delta) ≤ 1 + delta := by
      nlinarith [Real.sqrt_nonneg (1 + delta)]
    have hminus : 1 - delta ≤ Real.sqrt (1 - delta) := by
      nlinarith [Real.sqrt_nonneg (1 - delta)]
    have hroom : Real.sqrt (1 + delta) * (3 * (R / 16)) <
        Real.sqrt (1 - delta) * R := by
      have hplus2 : Real.sqrt (1 + delta) ≤ 2 := by linarith
      have hminus2 : (1 / 2 : ℝ) ≤ Real.sqrt (1 - delta) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hplus2 hR.le,
        mul_le_mul_of_nonneg_right hminus2 hR.le]
    intro a ha b hb
    obtain ⟨hlow, hupp⟩ := crossModel_toReal_transfer g (h k) (F k) q hR hdelta.le
      (by linarith) (by positivity : 0 ≤ R / 16) hRcompact (hRU.trans hsrc) hk hroom a ha b hb
    have hdist : riemannianEDistOf g a b ≤ ENNReal.ofReal (R / 8) := by
      calc
        riemannianEDistOf g a b ≤ riemannianEDistOf g a q + riemannianEDistOf g q b :=
          riemannianEDistOf_triangle g a q b
        _ = riemannianEDistOf g q a + riemannianEDistOf g q b := by
          rw [riemannianEDistOf_comm g a q]
        _ ≤ ENNReal.ofReal (R / 16) + ENNReal.ofReal (R / 16) := add_le_add ha hb
        _ = ENNReal.ofReal (R / 8) := by
          rw [← ENNReal.ofReal_add (by positivity : 0 ≤ R / 16) (by positivity : 0 ≤ R / 16)]
          congr 1
          ring
    have hD : (riemannianEDistOf g a b).toReal ≤ R / 8 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hdist
    have hD0 : 0 ≤ (riemannianEDistOf g a b).toReal := ENNReal.toReal_nonneg
    have herror : delta * (riemannianEDistOf g a b).toReal < epsilon := by
      have hm := mul_le_mul_of_nonneg_left (show (riemannianEDistOf g a b).toReal ≤ R + 1
        by linarith) hdelta.le
      exact hm.trans_lt hdeltasmall
    have hl := mul_le_mul_of_nonneg_right hminus hD0
    have hu := mul_le_mul_of_nonneg_right hplus hD0
    exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  · have hquad := eventually_pullback_metric_quadratic_bounds g U h F G hG hmetric
      hRcompact hRU (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hquad, hsource] with k hk hsrc
    have hKsource : K ⊆ (F k).source := (hKR.trans hRU).trans hsrc
    have hcapture := _root_.DifferentialGeometry.PartialDiffeomorph.closedBall_subset_image_closedBall_of_metric_lower g (h k) (F k) q
      (R := R / 16) (L := 2) (r := R / 64) (by positivity) (by norm_num)
      (by linarith) hKcompact hKsource (by
        intro x hx v
        have hlow := (hk x (hKR hx) v).1
        have hnonneg := _root_.DifferentialGeometry.metric_inner_self_nonneg
          (h k) (F k x) (mfderiv I I (F k) x v)
        nlinarith)
    refine ⟨hKsource, ?_⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hcapture hy
    have hxsource := hKsource hx
    have hytarget : y ∈ (F k).target := hxy ▸ (F k).map_source hxsource
    have hinverse : (F k).symm y = x := by
      rw [← hxy]
      exact (F k).left_inv hxsource
    exact ⟨hytarget, hinverse ▸ hx, (F k).right_inv hytarget⟩

end DifferentialGeometry.CheegerGromovCompactness
