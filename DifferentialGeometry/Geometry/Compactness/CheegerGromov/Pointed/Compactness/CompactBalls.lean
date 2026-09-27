import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.IncompleteLocal
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricAgreement

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

open private exists_uniform_injectivity_of_complete_metric_extension from
  DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalMetricExtension
open private PointedRiemannianConvergenceMaps.changeSourceMetric
  canonicalSourceData_derivNormSupOn_eq_of_source_metric_eqOn from
  DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricAgreement

private theorem eventually_lt_nat_add_one (R : ℝ) : ∀ᶠ n : ℕ in atTop, R < (n : ℝ) + 1 := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop R] with n hn
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem exists_complete_extensions_on_growing_balls
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (hcompact : ∀ R : ℝ, 0 < R →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R)) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ (g : ∀ n, SmoothRiemannianMetric I (X.obj (sigma n)).M)
        (U : ∀ n, Set (X.obj (sigma n)).M),
        (∀ n, RiemannianMetricComplete (g n)) ∧ (∀ n, IsOpen (U n)) ∧
        (∀ n : ℕ, riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint
          ((n : ℝ) + 1) ⊆ U n) ∧
        (∀ n, ∀ y ∈ U n, (g n).inner y = (X.obj (sigma n)).metric.inner y) ∧
        (∀ n y (v : TangentSpace I y),
          (X.obj (sigma n)).metric.inner y v v ≤ (g n).inner y v v) ∧
        (∀ n : ℕ, ∀ R : ℝ, R ≤ (n : ℝ) + 1 →
          riemannianBallOf (g n) (X.obj (sigma n)).basepoint R =
            riemannianBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint R) ∧
        ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → R < (n : ℝ) + 1 →
          riemannianClosedBallOf (g n) (X.obj (sigma n)).basepoint R =
            riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint R := by
  choose N hN using fun n : ℕ => eventually_atTop.mp (hcompact ((n : ℝ) + 1) (by positivity))
  obtain ⟨sigma, hsigma, hsigN⟩ := exists_strictMono_ge N
  choose g U hcomplete hU hKU hsame hmono _ hopen hclosed _ using fun n =>
    Geometry.exists_complete_metric_extension_of_riemannianClosedBall
      (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint (hN n (sigma n) (hsigN n))
  exact ⟨sigma, hsigma, g, U, hcomplete, hU, hKU, hsame, hmono, hopen, hclosed⟩

theorem exists_pointed_convergence_of_eventually_compact_balls
    (X : PointedRiemannianSeq.{u, uE, uH} I) (hconn : ∀ n, ConnectedSpace (X.obj n).M)
    (hcompact : ∀ R : ℝ, 0 < R →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R))
    (hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p C)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (L : PointedRiemannianManifold.{u, uE, uH} I)
        (F : PointedRiemannianConvergenceMaps X L f) (C : MetricConvergenceData F),
        (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
        MetricComplete L ∧ ConnectedSpace L.M ∧
        ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
          riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆ F.target n := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨sigma, hsigma, g, U, hc, hU, hKU, heq, hmono, hopen, hclosed⟩ :=
    exists_complete_extensions_on_growing_balls X hcompact
  let Y : PointedRiemannianSeq.{u, uE, uH} I :=
    { obj := fun n => { X.obj (sigma n) with metric := g n } }
  have hYc : SeqMetricComplete Y := ⟨fun n => (hc n).complete⟩
  have hYconn (n) : ConnectedSpace (Y.obj n).M := hconn (sigma n)
  have hYjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (Y.obj n) (Y.obj n).basepoint R p C := by
    intro R hR p
    obtain ⟨C, hC, hCbound⟩ := hjets R hR p
    refine ⟨C, hC, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hCbound, eventually_lt_nat_add_one R]
      with n hn hRn
    intro x hx
    have hxg : x ∈ riemannianClosedBallOf (X.obj (sigma n)).metric
        (X.obj (sigma n)).basepoint R := by
      change x ∈ riemannianClosedBallOf (g n) (X.obj (sigma n)).basepoint R at hx
      rwa [hclosed n R hR.le hRn] at hx
    have hxU := hKU n (riemannianClosedBallOf_mono _ _ hRn.le hxg)
    change curvDerivNorm p (g n) x ≤ C
    rw [curvDerivNorm_eq_of_metric_eventuallyEq (g n) (X.obj (sigma n)).metric x
      (by
        filter_upwards [(hU n).mem_nhds hxU] with y hy
        intro v w
        exact congrArg (fun B => B v w) (heq n y hy)) p]
    exact hn x hxg
  have hYinj : ∀ r : ℝ, 0 < r → ∃ η : ℝ, 0 < η ∧
      ∀ᶠ n in atTop, ∀ x : (Y.obj n).M,
        riemannianEDistOf (Y.obj n).metric (Y.obj n).basepoint x ≤ ENNReal.ofReal r →
          HasInjRadiusAt (Y.obj n) x η := by
    intro r hr
    obtain ⟨C, hC, hCbound⟩ := hjets (r + 1) (by linarith) 0
    obtain ⟨a, κ, ha, hκ, hra, hac, hv⟩ := hvol r (r + 1) hr (by linarith) C hC
    obtain ⟨iota, hiota, hinj⟩ :=
      exists_uniform_injectivity_of_complete_metric_extension.{u} (I := I) hκ
    refine ⟨iota * a, mul_pos hiota ha, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hCbound, hsigma.tendsto_atTop.eventually hv,
      eventually_lt_nat_add_one (r + 1)] with n hn hvn hRn
    intro x hx
    have hxg : x ∈ riemannianClosedBallOf (X.obj (sigma n)).metric
        (X.obj (sigma n)).basepoint r := by
      change x ∈ riemannianClosedBallOf (g n) (X.obj (sigma n)).basepoint r at hx
      rwa [hclosed n r hr.le (by linarith)] at hx
    exact hinj (X.obj (sigma n)) (g n) (U n) (hc n) (hU n) hr.le ha hra hac
      (fun z hz => hKU n (riemannianClosedBallOf_mono _ _ hRn.le hz)) (heq n) (hmono n)
      hn hvn x hxg
  obtain ⟨P, hdomain, href, hPconn, _, _, _⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      Y hYc hYconn hYjets hYinj
  let L := P.limit
  let _ : ConnectedSpace L.M := hPconn
  let F := P.maps
  let Cd := P.convergence.metrics
  have hagree : ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
      ∀ y ∈ riemannianBallOf (Y.obj (P.subseq k)).metric (Y.obj (P.subseq k)).basepoint R,
        (X.obj (sigma (P.subseq k))).metric.inner y = (Y.obj (P.subseq k)).metric.inner y := by
    intro R _
    filter_upwards [P.strictMono.tendsto_atTop.eventually (eventually_lt_nat_add_one R)]
      with k hk y hy
    change y ∈ riemannianBallOf (g (P.subseq k)) (X.obj (sigma (P.subseq k))).basepoint R at hy
    rw [hopen (P.subseq k) R hk.le] at hy
    have hy2 : riemannianEDistOf (X.obj (sigma (P.subseq k))).metric
        (X.obj (sigma (P.subseq k))).basepoint y ≤ ENNReal.ofReal R := le_of_lt hy
    exact (heq (P.subseq k) y (hKU (P.subseq k)
      (riemannianClosedBallOf_mono _ _ hk.le hy2))).symm
  let _ : PreconnectedSpace L.M := inferInstance
  have hupper : ∀ K : Set L.M, IsCompact K → ∀ᶠ k in atTop, K ⊆ F.source k ∧
      ∃ R : ℝ, 0 < R ∧ F.map k '' K ⊆
        riemannianBallOf (Y.obj (P.subseq k)).metric (Y.obj (P.subseq k)).basepoint R ∧
      ∀ y ∈ riemannianBallOf (Y.obj (P.subseq k)).metric (Y.obj (P.subseq k)).basepoint R,
        (X.obj (sigma (P.subseq k))).metric.inner y = (Y.obj (P.subseq k)).metric.inner y := by
    intro K hK
    obtain ⟨A, hA, himage⟩ :=
      F.exists_eventually_image_compact_subset_ball Cd href P.limit_complete hK
    filter_upwards [himage, hagree (A + 1) (by linarith)] with k hk hak
    refine ⟨hk.1, A + 1, by linarith, fun y hy => ?_, hak⟩
    exact lt_of_le_of_lt (hk.2 hy) (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by linarith⟩)
  let gX : ∀ n, SmoothRiemannianMetric I (Y.obj n).M := fun n => (X.obj (sigma n)).metric
  let F' := PointedRiemannianConvergenceMaps.changeSourceMetric F gX
  obtain ⟨C', hC', _⟩ := exists_metricConvergenceData_canonicalSourceData F' (by
    intro K hK p eps heps
    obtain ⟨N, hN⟩ := Cd.converges K hK p eps heps
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hupper K hK)
    refine ⟨max N J, fun k hk => ?_⟩
    have hkN := hN k ((le_max_left N J).trans hk)
    obtain ⟨hKsrc, R, _, himg, hag⟩ := hJ k ((le_max_right N J).trans hk)
    let V : Set (Y.obj (P.subseq k)).M :=
      riemannianBallOf (Y.obj (P.subseq k)).metric (Y.obj (P.subseq k)).basepoint R
    have hV : IsOpen V := isOpen_lt (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
    let W : TopologicalSpace.Opens L.M := ⟨F.source k ∩ F.map k ⁻¹' V,
      (F.partialDiffeomorph k).contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
        (F.partialDiffeomorph k).open_source hV⟩
    rw [canonicalSourceData_derivNormSupOn_eq_of_source_metric_eqOn F gX k W inter_subset_left K
      (fun x hx => ⟨hKsrc hx, himg ⟨x, hx, rfl⟩⟩) p (fun x hx => hag _ hx.2)]
    have h2 := hkN.2
    rw [show Cd.domain k = CanonicalMetricCompactness.canonicalSourceData F k from hdomain k] at h2
    exact h2)
  let hF : PointedRiemannianConvergenceMaps (X.subseq sigma) L P.subseq := F'
  let hC : MetricConvergenceData hF := C'
  let Fo := hF.ofSeqSubseq sigma
  let Co : MetricConvergenceData Fo := hC.ofSeqSubseq sigma
  have hCo (n : ℕ) : Co.domain n = CanonicalMetricCompactness.canonicalSourceData Fo n := by
    change MetricSourceData.ofSeqSubseq sigma n (C'.domain n) = _
    rw [hC' n]
    rfl
  obtain ⟨Cf, hCf, hreff⟩ := exists_metricConvergenceData_canonicalSourceData Fo (by
    intro K hK p eps heps
    obtain ⟨k0, hk0⟩ := Co.converges K hK p eps heps
    exact ⟨k0, fun k hk => by rw [← hCo k]; exact (hk0 k hk).2⟩)
  refine ⟨sigma ∘ P.subseq, hsigma.comp P.strictMono, L, Fo, Cf, hCf, P.limit_complete,
    hPconn, ?_⟩
  intro R hR
  filter_upwards [Fo.eventually_ball_subset_image_closed_ball Cf hreff P.limit_complete
    L.basepoint (A := R + 1) (R := 2 * (R + 1) + 1) one_lt_two (by linarith)] with n hn
  intro y hy
  have hy' : y ∈ riemannianBallOf (X.obj ((sigma ∘ P.subseq) n)).metric
      (Fo.map n L.basepoint) (R + 1) := by
    change riemannianEDistOf _ (Fo.partialDiffeomorph n L.basepoint) y < _
    rw [Fo.basepoint_map n]
    exact lt_of_le_of_lt hy (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨x, hx, rfl⟩ := hn.2 hy'
  exact (Fo.partialDiffeomorph n).map_source (hn.1 hx)

theorem exists_pointed_convergence_on_base_components_of_eventually_compact_balls
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (hcompact : ∀ R : ℝ, 0 < R →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R))
    (hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p C)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (L : PointedRiemannianManifold.{u, uE, uH} I)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent L f),
        let U := fun i => connectedComponentOpen (I := I) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ C : MetricConvergenceData F',
        (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        MetricComplete L ∧ ConnectedSpace L.M ∧
        ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
          riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆ F'.target n := by
  have hcompactC : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.connectedComponent.obj n).metric
        (X.connectedComponent.obj n).basepoint R) := by
    intro R hR
    filter_upwards [hcompact R hR] with n hn
    exact (X.obj n).isCompact_closedBall_connectedComponent R hn
  have hjetsC : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.connectedComponent.obj n)
        (X.connectedComponent.obj n).basepoint R p C := by
    intro R hR p
    obtain ⟨C, hC, hCn⟩ := hjets R hR p
    exact ⟨C, hC, hCn.mono fun n hn => hn.connectedComponent⟩
  have hvolC : ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.connectedComponent.obj n).metric
          (X.connectedComponent.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.connectedComponent.obj n).M
            (X.connectedComponent.obj n).metric
            (riemannianBallOf (X.connectedComponent.obj n).metric x a) :=
    fun r R hr hrR => X.inner_ball_volume_lower_bound_connectedComponent (R + 1)
      (fun r' R' hr' hrR' _ => hvol r' R' hr' hrR') r R hr hrR (by linarith)
  obtain ⟨f, hf, L, F, C, hC, hLc, hLconn, hcapture⟩ :=
    exists_pointed_convergence_of_eventually_compact_balls X.connectedComponent
      (fun n => (X.obj n).connectedComponent_connected) hcompactC hjetsC hvolC
  let U := fun i => connectedComponentOpen (I := I) (X.obj i).basepoint
  let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
  obtain ⟨C', hC'⟩ := F.exists_canonical_metric_convergence_liftTargetOpen U hp C hC
  refine ⟨f, hf, L, F, C', hC', hLc, hLconn, fun R hR => ?_⟩
  filter_upwards [hcapture R hR] with n hn y hy
  have hyU : y ∈ (U (f n) : Set (X.obj (f n)).M) := by
    apply Geometry.Metric.edistOf_ball_subset_connCompOpen
      (I := I) (X.obj (f n)).metric (X.obj (f n)).basepoint (R + 1)
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  let y' : (X.connectedComponent.obj (f n)).M := ⟨y, hyU⟩
  have hy' : y' ∈ riemannianClosedBallOf (X.connectedComponent.obj (f n)).metric
      (X.connectedComponent.obj (f n)).basepoint R :=
    (Set.ext_iff.mp ((X.obj (f n)).connectedComponent_closedBall R) y').mpr hy
  rw [PointedRiemannianConvergenceMaps.liftTargetOpen_target (U := U) (hp := hp) F n]
  exact ⟨y', hn hy', rfl⟩

end DifferentialGeometry.CheegerGromovCompactness

end
