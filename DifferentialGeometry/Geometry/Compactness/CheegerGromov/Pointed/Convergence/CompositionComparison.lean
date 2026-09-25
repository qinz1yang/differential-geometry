import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Geometry.Comparison.MetricDistanceTransfer
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (crossModel_edist_le_of_metric_upper crossModel_toReal_transfer)

universe u uM uN uP uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H0 : Type uH} [TopologicalSpace H0] {I : ModelWithCorners ℝ E H0}
  {M : Type uM} [MetricSpace M] [ChartedSpace H0 M] [IsManifold I ∞ M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H0 N] [IsManifold I ∞ N]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem exists_terminal_end_comparison_domain
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (p : M) (X : PointedRiemannianSeq.{u} I)
    (A : ∀ i, PartialDiffeomorph I I M (X.obj i).M ∞)
    (hsource : ∀ K : Set M, IsCompact K → ∀ᶠ i in atTop, K ⊆ (A i).source)
    (hbase : ∀ i, A i p = (X.obj i).basepoint)
    (G : ℕ → SmoothRiemannianMetric I M)
    (hG : ∀ i, ∀ y ∈ (A i).source, ∀ v w : TangentSpace I y,
      (G i).inner y v w = (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y v) (mfderiv I I (A i) y w))
    (hconv : ∀ K : Set M, IsCompact K → MetricCPConvergenceOn K 0 G g g)
    (H : ℕ → SmoothRiemannianMetric I N) (x : ℕ → N)
    (B : ∀ i, PartialDiffeomorph I I N (X.obj i).M ∞)
    {R : ℝ} (hR : 0 < R)
    (hB : ∀ i, riemannianClosedBallOf (H i) (x i) R ⊆ (B i).source)
    (hcapture : ∀ i, riemannianClosedBallOf (X.obj i).metric
      (X.obj i).basepoint (R / 4) ⊆ (B i) '' riemannianClosedBallOf (H i) (x i) R) :
    ∃ s : ℝ, 0 < s ∧ s < R / 10 ∧
      IsCompact (riemannianClosedBallOf g p (8 * s)) ∧
      ∀ᶠ i in atTop,
        riemannianClosedBallOf g p (2 * s) ⊆ ((A i).trans (B i).symm).source ∧
        ∀ y ∈ riemannianClosedBallOf g p (2 * s),
          (B i).symm (A i y) ∈ riemannianClosedBallOf (H i) (x i) R := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨r0, hr0, hcompact⟩ := Metric.exists_isCompact_closedBall p
  let s := min (r0 / 8) (R / 100)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hs0 : 8 * s ≤ r0 := by linarith [min_le_left (r0 / 8) (R / 100)]
  have hsR : s ≤ R / 100 := min_le_right _ _
  have hball (r : ℝ) (hr : 0 ≤ r) : riemannianClosedBallOf g p r = Metric.closedBall p r := by
    ext y
    change riemannianEDistOf g p y ≤ ENNReal.ofReal r ↔ dist y p ≤ r
    rw [← hmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff hr, dist_comm]
  let K := riemannianClosedBallOf g p (8 * s)
  have hK : IsCompact K := by
    rw [show K = Metric.closedBall p (8 * s) from hball _ (by positivity)]
    exact hcompact.of_isClosed_subset Metric.isClosed_closedBall (Metric.closedBall_subset_closedBall hs0)
  have hsub : riemannianClosedBallOf g p (2 * s) ⊆ K :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  obtain ⟨n0, hn0⟩ := hconv K hK 1 zero_lt_one
  refine ⟨s, hs, by linarith, hK, ?_⟩
  filter_upwards [hsource K hK, eventually_ge_atTop n0] with i hi hin
  have hupper : ∀ y ∈ K, ∀ v : TangentSpace I y,
      (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y v) (mfderiv I I (A i) y v) ≤
        (2 : ℝ) ^ 2 * g.inner y v v := by
    intro y hy v
    have hb := inner_bounds_of_metricTensorErrorNorm_le (G i) g (K := K)
      (fun z hz => (derivNorm_le_sup hK (le_refl 0) (G i) g g hz).trans (hn0 i hin).le) y hy v
    rw [hG i y (hi hy)] at hb
    have hg := metric_inner_self_nonneg g y v
    nlinarith only [hb.2, hg]
  have hmaps (y : M) (hy : y ∈ riemannianClosedBallOf g p (2 * s)) :
      ∃ z ∈ riemannianClosedBallOf (H i) (x i) R, B i z = A i y := by
    apply hcapture i
    have hp : p ∈ riemannianClosedBallOf g p (2 * s) := by
      change riemannianEDistOf g p p ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le
    have hd := crossModel_edist_le_of_metric_upper g (X.obj i).metric
      (A i) p (by norm_num : 0 < (2 : ℝ)) (show 0 ≤ 2 * s by positivity)
      (show 3 * (2 * s) < 8 * s by linarith) hi hupper hp hy
    rw [hbase] at hd
    change riemannianEDistOf (X.obj i).metric (X.obj i).basepoint (A i y) ≤ _
    calc
      _ ≤ ENNReal.ofReal 2 * riemannianEDistOf g p y := hd
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (2 * s) := mul_le_mul' le_rfl hy
      _ = ENNReal.ofReal (4 * s) := by
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (R / 4) := ENNReal.ofReal_le_ofReal (by linarith)
  constructor
  · intro y hy
    obtain ⟨z, hz, heq⟩ := hmaps y hy
    change y ∈ (A i).source ∧ A i y ∈ (B i).target
    exact ⟨hi (hsub hy), heq ▸ (B i).map_source (hB i hz)⟩
  · intro y hy
    obtain ⟨z, hz, heq⟩ := hmaps y hy
    rw [← heq]
    erw [(B i).left_inv (hB i hz)]
    exact hz


variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H0 P] [IsManifold I ∞ P]

omit [FiniteDimensional ℝ E] in
private theorem inverse_composition_inner_bounds
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (s : SmoothRiemannianMetric I P)
    (A : PartialDiffeomorph I I M P ∞) (B : PartialDiffeomorph I I N P ∞)
    {x : M} (hx : x ∈ (A.trans B.symm).source)
    {alpha beta : ℝ} (hb0 : 0 ≤ beta) (hb1 : beta < 1)
    (hA : ∀ v : TangentSpace I x,
      (1 - alpha) * g.inner x v v ≤ s.inner (A x)
        (mfderiv I I A x v) (mfderiv I I A x v) ∧
      s.inner (A x) (mfderiv I I A x v) (mfderiv I I A x v) ≤
        (1 + alpha) * g.inner x v v)
    (hB : ∀ v : TangentSpace I (A.trans B.symm x),
      (1 - beta) * h.inner (A.trans B.symm x) v v ≤
        s.inner (B (A.trans B.symm x))
          (mfderiv I I B (A.trans B.symm x) v) (mfderiv I I B (A.trans B.symm x) v) ∧
      s.inner (B (A.trans B.symm x))
          (mfderiv I I B (A.trans B.symm x) v) (mfderiv I I B (A.trans B.symm x) v) ≤
        (1 + beta) * h.inner (A.trans B.symm x) v v) :
    ∀ v : TangentSpace I x,
      (1 - alpha) / (1 + beta) * g.inner x v v ≤
        h.inner (A.trans B.symm x) (mfderiv I I (A.trans B.symm) x v)
          (mfderiv I I (A.trans B.symm) x v) ∧
      h.inner (A.trans B.symm x) (mfderiv I I (A.trans B.symm) x v)
          (mfderiv I I (A.trans B.symm) x v) ≤
        (1 + alpha) / (1 - beta) * g.inner x v v := by
  let C := A.trans B.symm
  have heq : (B : N → P) ∘ C =ᶠ[𝓝 x] A := by
    filter_upwards [C.open_source.mem_nhds hx] with y hy
    exact B.right_inv hy.2
  have hpoint : B (C x) = A x := heq.eq_of_nhds
  have hd (v : TangentSpace I x) :
      mfderiv I I B (C x) (mfderiv I I C x v) = mfderiv I I A x v := by
    have hc := C.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hx
    have hb := B.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) (B.map_target hx.2)
    exact (mfderiv_comp_apply x hb hc v).symm.trans
      (DFunLike.congr_fun (heq.mfderiv_eq (I := I) (I' := I)) v)
  intro v
  have hh := hB (mfderiv I I C x v)
  have ha := hA v
  change (1 - beta) * h.inner (C x) (mfderiv I I C x v) (mfderiv I I C x v) ≤
    s.inner (B (C x)) (mfderiv I I B (C x) (mfderiv I I C x v))
      (mfderiv I I B (C x) (mfderiv I I C x v)) ∧
    s.inner (B (C x)) (mfderiv I I B (C x) (mfderiv I I C x v))
      (mfderiv I I B (C x) (mfderiv I I C x v)) ≤
    (1 + beta) * h.inner (C x) (mfderiv I I C x v) (mfderiv I I C x v) at hh
  erw [hd v, hpoint] at hh
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + beta)]
    nlinarith only [ha.1, hh.2]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < 1 - beta)]
    nlinarith only [ha.2, hh.1]


private theorem exists_terminal_end_metric_comparison
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (p : M) (X : PointedRiemannianSeq.{u} I)
    (A : ∀ i, PartialDiffeomorph I I M (X.obj i).M ∞)
    (hsource : ∀ K : Set M, IsCompact K → ∀ᶠ i in atTop, K ⊆ (A i).source)
    (hbase : ∀ i, A i p = (X.obj i).basepoint)
    (G : ℕ → SmoothRiemannianMetric I M)
    (hG : ∀ i, ∀ y ∈ (A i).source, ∀ v w : TangentSpace I y,
      (G i).inner y v w = (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y v) (mfderiv I I (A i) y w))
    (hconv : ∀ K : Set M, IsCompact K → MetricCPConvergenceOn K 0 G g g)
    (H : ℕ → SmoothRiemannianMetric I N) (x : ℕ → N)
    (B : ∀ i, PartialDiffeomorph I I N (X.obj i).M ∞)
    {R : ℝ} (hR : 0 < R)
    (hB : ∀ i, riemannianClosedBallOf (H i) (x i) R ⊆ (B i).source)
    (hBbase : ∀ i, B i (x i) = (X.obj i).basepoint)
    (hcapture : ∀ i, riemannianClosedBallOf (X.obj i).metric
      (X.obj i).basepoint (R / 4) ⊆ (B i) '' riemannianClosedBallOf (H i) (x i) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf (H i) (x i) R, ∀ v : TangentSpace I y,
        (1 - eta) * (H i).inner y v v ≤ (X.obj i).metric.inner (B i y)
          (mfderiv I I (B i) y v) (mfderiv I I (B i) y v) ∧
        (X.obj i).metric.inner (B i y)
          (mfderiv I I (B i) y v) (mfderiv I I (B i) y v) ≤
            (1 + eta) * (H i).inner y v v) :
    ∃ s : ℝ, 0 < s ∧ s < R / 10 ∧
      IsCompact (riemannianClosedBallOf g p (8 * s)) ∧
      (∀ᶠ i in atTop,
        riemannianClosedBallOf g p (2 * s) ⊆ ((A i).trans (B i).symm).source ∧
        ∀ y ∈ riemannianClosedBallOf g p (2 * s),
          (B i).symm (A i y) ∈ riemannianClosedBallOf (H i) (x i) R) ∧
      (∀ i, (A i).trans (B i).symm p = x i) ∧
      ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
        ∀ y ∈ riemannianClosedBallOf g p (2 * s), ∀ v : TangentSpace I y,
          (1 - eps) * g.inner y v v ≤
            (H i).inner ((A i).trans (B i).symm y)
              (mfderiv I I ((A i).trans (B i).symm) y v)
              (mfderiv I I ((A i).trans (B i).symm) y v) ∧
          (H i).inner ((A i).trans (B i).symm y)
              (mfderiv I I ((A i).trans (B i).symm) y v)
              (mfderiv I I ((A i).trans (B i).symm) y v) ≤
            (1 + eps) * g.inner y v v := by
  obtain ⟨s, hs, hsR, hK, hdomain⟩ := exists_terminal_end_comparison_domain
    g hmetric p X A hsource hbase G hG hconv H x B hR hB hcapture
  refine ⟨s, hs, hsR, hK, hdomain, ?_, ?_⟩
  · intro i
    change (B i).symm (A i p) = x i
    rw [hbase, ← hBbase]
    apply (B i).left_inv
    apply hB i
    change riemannianEDistOf (H i) (x i) (x i) ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  intro eps heps
  let eta := min (eps / 8) (1 / 8)
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have hetaE : eta ≤ eps / 8 := min_le_left _ _
  have heta8 : eta ≤ 1 / 8 := min_le_right _ _
  have hlow : 1 - eps ≤ (1 - eta) / (1 + eta) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + eta)).mpr
    nlinarith only [hetaE, heta, heps, mul_pos heps heta]
  have hhigh : (1 + eta) / (1 - eta) ≤ 1 + eps := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - eta)).mpr
    nlinarith only [hetaE, mul_le_mul_of_nonneg_left heta8 heps.le]
  obtain ⟨i0, hi0⟩ := hconv _ hK eta heta
  have hsub : riemannianClosedBallOf g p (2 * s) ⊆ riemannianClosedBallOf g p (8 * s) :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  filter_upwards [hdomain, hBconv eta heta, eventually_ge_atTop i0] with i hi hBi hii
  intro y hy v
  have hAi : ∀ w : TangentSpace I y,
      (1 - eta) * g.inner y w w ≤ (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y w) (mfderiv I I (A i) y w) ∧
      (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y w) (mfderiv I I (A i) y w) ≤
        (1 + eta) * g.inner y w w := by
    intro w
    have hb := inner_bounds_of_metricTensorErrorNorm_le (G i) g
      (K := riemannianClosedBallOf g p (8 * s))
      (fun z hz => (derivNorm_le_sup hK (le_refl 0) (G i) g g hz).trans (hi0 i hii).le)
      y (hsub hy) w
    rw [hG i y (hi.1 hy).1] at hb
    exact hb
  have hb := inverse_composition_inner_bounds g (H i) (X.obj i).metric
    (A i) (B i) (hi.1 hy) heta.le (by linarith) hAi
    (hBi _ (hi.2 y hy)) v
  have hn := metric_inner_self_nonneg g y v
  exact ⟨(mul_le_mul_of_nonneg_right hlow hn).trans hb.1,
    hb.2.trans (mul_le_mul_of_nonneg_right hhigh hn)⟩

private theorem exists_terminal_end_distance_comparison [T2Space N]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (p : M) (H : ℕ → SmoothRiemannianMetric I N) (x : ℕ → N)
    (C : ℕ → PartialDiffeomorph I I M N ∞)
    {s : ℝ} (hs : 0 < s)
    (hcompact : IsCompact (riemannianClosedBallOf g p (8 * s)))
    (hsource : ∀ᶠ i in atTop, riemannianClosedBallOf g p (2 * s) ⊆ (C i).source)
    (hbase : ∀ i, C i p = x i)
    (hmetricconv : ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf g p (2 * s), ∀ v : TangentSpace I y,
        (1 - eps) * g.inner y v v ≤ (H i).inner (C i y)
          (mfderiv I I (C i) y v) (mfderiv I I (C i) y v) ∧
        (H i).inner (C i y) (mfderiv I I (C i) y v)
          (mfderiv I I (C i) y v) ≤ (1 + eps) * g.inner y v v) :
    ∃ r : ℝ, 0 < r ∧ r < s ∧ IsCompact (Metric.closedBall p r) ∧
      (∀ᶠ i in atTop, Metric.closedBall p r ⊆ (C i).source ∧
        riemannianClosedBallOf (H i) (x i) (r / 4) ⊆ (C i) '' Metric.closedBall p r) ∧
      ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
        ∀ a ∈ Metric.closedBall p r, ∀ b ∈ Metric.closedBall p r,
          |(riemannianEDistOf (H i) (C i a) (C i b)).toReal - dist a b| < eps := by
  let r := s / 10
  have hr : 0 < r := by positivity
  have hball (t : ℝ) (ht : 0 ≤ t) : riemannianClosedBallOf g p t = Metric.closedBall p t := by
    ext y
    change riemannianEDistOf g p y ≤ ENNReal.ofReal t ↔ dist y p ≤ t
    rw [← hmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff ht, dist_comm]
  have hc (t : ℝ) (ht : 0 ≤ t) (hts : t ≤ 8 * s) :
      IsCompact (riemannianClosedBallOf g p t) := by
    rw [hball _ ht]
    rw [hball _ (by positivity)] at hcompact
    exact hcompact.of_isClosed_subset Metric.isClosed_closedBall
      (Metric.closedBall_subset_closedBall hts)
  have hr2 : r ≤ 2 * s := by dsimp [r]; linarith
  have hsub : Metric.closedBall p r ⊆ riemannianClosedBallOf g p (2 * s) := by
    rw [← hball _ hr.le]
    exact riemannianClosedBallOf_mono _ _ hr2
  refine ⟨r, hr, by dsimp [r]; linarith, by rw [← hball _ hr.le]; exact hc r hr.le (by linarith), ?_, ?_⟩
  · filter_upwards [hsource, hmetricconv (1 / 4) (by norm_num)] with i hi hmi
    refine ⟨hsub.trans hi, ?_⟩
    rw [← hbase, ← hball _ hr.le]
    apply DifferentialGeometry.PartialDiffeomorph.closedBall_subset_image_closedBall_of_metric_lower g (H i) (C i) p hr
      (by norm_num : 0 < (2 : ℝ)) (by linarith)
      (hc r hr.le (by linarith))
      ((riemannianClosedBallOf_mono _ _ hr2).trans hi)
    intro y hy v
    have hh := (hmi y (riemannianClosedBallOf_mono _ _ hr2 hy) v).1
    have hg := metric_inner_self_nonneg g y v
    nlinarith only [hh, hg]
  intro eps heps
  let eta := min (eps / (4 * r + 1)) (1 / 4)
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have heta4 : eta ≤ 1 / 4 := min_le_right _ _
  have hetaE : eta * (4 * r + 1) ≤ eps :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  filter_upwards [hsource, hmetricconv eta heta] with i hi hmi
  have hplus : Real.sqrt (1 + eta) ≤ 1 + eta :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hminus : 1 - eta ≤ Real.sqrt (1 - eta) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [heta.le, heta4]
  have hroom : Real.sqrt (1 + eta) * (3 * r) < Real.sqrt (1 - eta) * (2 * s) := by
    have hu : Real.sqrt (1 + eta) ≤ 3 / 2 := hplus.trans (by linarith)
    have hl : 1 / 2 ≤ Real.sqrt (1 - eta) := (by linarith : (1 / 2 : ℝ) ≤ 1 - eta).trans hminus
    have hrdef : r = s / 10 := rfl
    nlinarith only [mul_le_mul_of_nonneg_right hu (show 0 ≤ 3 * r by positivity),
      mul_le_mul_of_nonneg_right hl (show 0 ≤ 2 * s by positivity), hs, hrdef]
  have hd := crossModel_toReal_transfer g (H i) (C i) p (show 0 < 2 * s by positivity)
    heta.le (by linarith) hr.le (hc _ (by positivity) (by linarith)) hi hmi hroom
  intro a ha b hb
  have hD : (riemannianEDistOf g a b).toReal = dist a b := by
    rw [← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hpairs := hd a (by rwa [hball _ hr.le]) b (by rwa [hball _ hr.le])
  change Real.sqrt (1 - eta) * (riemannianEDistOf g a b).toReal ≤ (riemannianEDistOf (H i) (C i a) (C i b)).toReal ∧
    (riemannianEDistOf (H i) (C i a) (C i b)).toReal ≤ Real.sqrt (1 + eta) * (riemannianEDistOf g a b).toReal at hpairs
  rw [hD] at hpairs
  have hdiam : dist a b ≤ 2 * r := by
    have ht := dist_triangle a p b
    rw [dist_comm p b] at ht
    have ha' : dist a p ≤ r := ha
    have hb' : dist b p ≤ r := hb
    linarith only [ht, ha', hb']
  have hl := (mul_le_mul_of_nonneg_right hminus (dist_nonneg : 0 ≤ dist a b)).trans hpairs.1
  have hu := hpairs.2.trans (mul_le_mul_of_nonneg_right hplus (dist_nonneg : 0 ≤ dist a b))
  have herr : eta * dist a b < eps := by
    nlinarith only [mul_le_mul_of_nonneg_left hdiam heta.le, hetaE, heta, hr,
      mul_pos heta hr]
  exact abs_lt.mpr ⟨by nlinarith only [hl, herr], by nlinarith only [hu, herr]⟩

theorem exists_inverse_composition_distance_comparison [T2Space N]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (p : M) (X : PointedRiemannianSeq.{u} I)
    (A : ∀ i, PartialDiffeomorph I I M (X.obj i).M ∞)
    (hsource : ∀ K : Set M, IsCompact K → ∀ᶠ i in atTop, K ⊆ (A i).source)
    (hbase : ∀ i, A i p = (X.obj i).basepoint)
    (G : ℕ → SmoothRiemannianMetric I M)
    (hG : ∀ i, ∀ y ∈ (A i).source, ∀ v w : TangentSpace I y,
      (G i).inner y v w = (X.obj i).metric.inner (A i y)
        (mfderiv I I (A i) y v) (mfderiv I I (A i) y w))
    (hconv : ∀ K : Set M, IsCompact K → MetricCPConvergenceOn K 0 G g g)
    (H : ℕ → SmoothRiemannianMetric I N) (x : ℕ → N)
    (B : ∀ i, PartialDiffeomorph I I N (X.obj i).M ∞)
    {R : ℝ} (hR : 0 < R)
    (hB : ∀ i, riemannianClosedBallOf (H i) (x i) R ⊆ (B i).source)
    (hBbase : ∀ i, B i (x i) = (X.obj i).basepoint)
    (hcapture : ∀ i, riemannianClosedBallOf (X.obj i).metric
      (X.obj i).basepoint (R / 4) ⊆ (B i) '' riemannianClosedBallOf (H i) (x i) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf (H i) (x i) R, ∀ v : TangentSpace I y,
        (1 - eta) * (H i).inner y v v ≤ (X.obj i).metric.inner (B i y)
          (mfderiv I I (B i) y v) (mfderiv I I (B i) y v) ∧
        (X.obj i).metric.inner (B i y)
          (mfderiv I I (B i) y v) (mfderiv I I (B i) y v) ≤
            (1 + eta) * (H i).inner y v v) :
    let C := fun i => (A i).trans (B i).symm
    ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf g p r) ∧
      (∀ i, C i p = x i) ∧
      (∀ᶠ i in atTop, riemannianClosedBallOf g p r ⊆ (C i).source ∧
        riemannianClosedBallOf (H i) (x i) (r / 4) ⊆
          (C i) '' riemannianClosedBallOf g p r) ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        ∀ a ∈ riemannianClosedBallOf g p r, ∀ b ∈ riemannianClosedBallOf g p r,
          |(riemannianEDistOf (H i) (C i a) (C i b)).toReal - (riemannianEDistOf g a b).toReal| < eta := by
  obtain ⟨s, hs, _, hK, hdomain, hbaseC, hmetricC⟩ :=
    exists_terminal_end_metric_comparison g hmetric p X A hsource hbase G hG hconv
      H x B hR hB hBbase hcapture hBconv
  obtain ⟨r, hr, _, hKr, hcaptureC, hdist⟩ :=
    exists_terminal_end_distance_comparison g hmetric p H x
      (fun i => (A i).trans (B i).symm) hs hK
      (hdomain.mono fun _ hi => hi.1) hbaseC hmetricC
  have hball : riemannianClosedBallOf g p r = Metric.closedBall p r := by
    ext y
    change riemannianEDistOf g p y ≤ ENNReal.ofReal r ↔ dist y p ≤ r
    rw [← hmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
  refine ⟨r, hr, hball.symm ▸ hKr, hbaseC, ?_, ?_⟩
  · simpa only [hball] using hcaptureC
  · intro eta heta
    filter_upwards [hdist eta heta] with i hi
    intro a ha b hb
    have hd : (riemannianEDistOf g a b).toReal = dist a b := by
      rw [← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    rw [hd]
    exact hi a (hball ▸ ha) b (hball ▸ hb)

end DifferentialGeometry.CheegerGromovCompactness
