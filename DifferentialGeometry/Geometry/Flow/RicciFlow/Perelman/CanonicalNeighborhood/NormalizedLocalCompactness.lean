import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedTerminalDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceNoncollapse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Local
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.LocalProperness

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem NormalizedSequence.eventually_hasInjRadiusAt_on_closed_ball_of_curvature_bound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {kappa' : ℝ} (hnc : X.TerminalSliceNoncollapsed kappa') {r R C : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hbound : ∀ᶠ i in atTop, ∀ y, metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < R →
      curvDerivNorm 0 ((X.term i).S.base.metric 0) y ≤ C) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ i in atTop, ∀ y : (X.term i).M,
      riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ ENNReal.ofReal r →
        HasInjRadiusAt ((X.term i).atTime 0) y eta := by
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hnc.1
  let a : ℝ := min ((C ^ 2 + 1)⁻¹) (R - r)
  have ha : 0 < a := lt_min (by positivity) (sub_pos.mpr hrR)
  have haC : a ≤ (C ^ 2 + 1)⁻¹ := min_le_left _ _
  have habuffer : a ≤ R - r := min_le_right _ _
  have haone : a ≤ 1 := haC.trans
    ((inv_le_one₀ (by positivity : 0 < C ^ 2 + 1)).mpr (by nlinarith))
  have hac : a * C ^ 2 ≤ 1 := by
    calc
      _ ≤ (C ^ 2 + 1)⁻¹ * (C ^ 2 + 1) :=
        mul_le_mul haC (by linarith) (sq_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hascaled : a ^ 4 * C ^ 2 ≤ 1 := by
    calc
      _ = a ^ 3 * (a * C ^ 2) := by ring
      _ ≤ 1 ^ 3 * 1 := mul_le_mul (pow_le_pow_left₀ ha.le haone 3) hac
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  refine ⟨iota * a, mul_pos hiota ha, ?_⟩
  filter_upwards [hnc.2, hbound] with i hi hbi y hy
  have hzero : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hcurv : ∀ z ∈ riemannianBallOf ((X.term i).S.base.metric 0) y a,
      a ^ 4 * Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04At ((X.term i).S.base.metric 0) z) ≤ 1 := by
    intro z hz
    have hz' : metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint z < R := by
      have hd : riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint z <
          ENNReal.ofReal R := by
        calc
          _ ≤ riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint y +
              riemannianEDistOf ((X.term i).S.base.metric 0) y z :=
            riemannianEDistOf_triangle _ _ _ _
          _ < ENNReal.ofReal r + ENNReal.ofReal a :=
            ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy) hy hz
          _ = ENNReal.ofReal (r + a) := (ENNReal.ofReal_add hr ha.le).symm
          _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by linarith)
      exact (ENNReal.toReal_lt_toReal hd.ne_top ENNReal.ofReal_ne_top).mpr hd |>.trans_eq
        (ENNReal.toReal_ofReal (hr.trans hrR.le))
    have hj := hbi z hz'
    have hsq : Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04At ((X.term i).S.base.metric 0) z) ≤ C ^ 2 := by
      apply le_sq_of_sqrt_le (Tensor0SBundle.normSq0S_nonneg _ _ _ _)
      change Real.sqrt (Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04 ((X.term i).S.base.metric 0) z)) ≤ C at hj
      rwa [metricRm04_apply] at hj
    exact (mul_le_mul_of_nonneg_left hsq (pow_nonneg ha.le 4)).trans hascaled
  let B : FlowMetricBall (X.term i).S ⟨0, hzero⟩ := ⟨y, a, ha⟩
  have hvol := (hi _ rfl B haone hcurv).2
  have hvol' : ENNReal.ofReal (kappa' * a ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure I3 (X.term i).M ((X.term i).S.base.metric 0)
        (riemannianBallOf ((X.term i).S.base.metric 0) y a) := by
    rw [ENNReal.ofReal_mul hnc.1.le, ENNReal.ofReal_pow ha.le]
    exact hvol
  exact hasInjRadiusAt_of_expMap_injOn ((X.term i).atTime 0) y (mul_pos hiota ha)
    (hinj _ _ ⟨X.complete i 0 hzero⟩ y a ha hcurv hvol')

theorem exists_terminal_bidirectional_pairwise_metric_approximation_within_radius
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ rho : ℝ, 0 < rho →
              (∀ r : ℝ, 0 < r → r < rho → CurvatureBoundedWithin X r) →
              ∃ f : ℕ → ℕ, StrictMono f ∧
                ∀ r : ℝ, 0 < r → r < rho → ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ p : ℕ,
                  ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
                    ∃ Ψ : PartialDiffeomorph I3 I3 (X.term (f k)).M (X.term (f l)).M ∞,
                      Ψ (X.term (f k)).basepoint = (X.term (f l)).basepoint ∧
                      Nonempty (PartialDiffeomorphMetricApproximation
                        (riemannianClosedBallOf ((X.term (f k)).S.base.metric 0)
                          (X.term (f k)).basepoint r)
                        eta p Ψ ((X.term (f k)).S.base.metric 0)
                          ((X.term (f l)).S.base.metric 0)) ∧
                      Nonempty (PartialDiffeomorphMetricApproximation
                        (riemannianClosedBallOf ((X.term (f l)).S.base.metric 0)
                          (X.term (f l)).basepoint r)
                        eta p Ψ.symm ((X.term (f l)).S.base.metric 0)
                          ((X.term (f k)).S.base.metric 0)) := by
  obtain ⟨epsSub, hepsSub, hsublevel⟩ := exists_curvDerivNorm_le_on_scalar_sublevel hkappa
  obtain ⟨epsNC, hepsNC, hnc⟩ := exists_terminalSliceNoncollapsed.{u} hkappa
  refine ⟨min epsSub epsNC, lt_min hepsSub hepsNC, ?_⟩
  intro eps heps hle' sigma hsigma Phi hPhi X rho hrho hinner
  have hle : eps ≤ epsSub := hle'.trans (min_le_left _ _)
  obtain ⟨kappa', -, hncX⟩ := hnc Phi hPhi
  have hncX := hncX eps heps (hle'.trans (min_le_right _ _)) sigma X
  have hb : ∀ r : ℝ, 0 < r → r < rho → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i y, metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r →
        curvDerivNorm m ((X.term i).S.base.metric 0) y ≤ C := by
    intro r hr hrho m
    obtain ⟨A, hA⟩ := hinner r hr hrho
    obtain ⟨C, hC, hc⟩ := hsublevel eps heps hle sigma hsigma Phi hPhi X A m
    exact ⟨C, hC, fun i y hy => hc i y (hA i y hy)⟩
  let Y := X.toFlowSequence.atTime 0
  have hcomplete : SeqMetricComplete Y := by
    constructor
    intro i
    apply X.complete i 0
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  apply exists_subsequence_bidirectional_pairwise_metric_approximation_within_radius
    Y hcomplete X.connected hrho
  · intro r hr hrrho m
    obtain ⟨C, hC, hc⟩ := hb ((r + rho) / 2) (by linarith) (by linarith) m
    refine ⟨C, hC, Filter.Eventually.of_forall fun i y hy => hc i y ?_⟩
    exact (ENNReal.toReal_le_of_le_ofReal hr.le hy).trans_lt (by linarith)
  · intro r hr hrrho
    obtain ⟨C, _, hc⟩ := hb ((r + rho) / 2) (by linarith) (by linarith) 0
    exact X.eventually_hasInjRadiusAt_on_closed_ball_of_curvature_bound
      hncX hr.le (by linarith) (Eventually.of_forall hc)

theorem exists_terminal_pairwise_metric_approximation_within_radius
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ rho : ℝ, 0 < rho →
              (∀ r : ℝ, 0 < r → r < rho → CurvatureBoundedWithin X r) →
              ∃ f : ℕ → ℕ, StrictMono f ∧
                ∀ r : ℝ, 0 < r → r < rho → ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ p : ℕ,
                  ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
                    ∃ Ψ : PartialDiffeomorph I3 I3 (X.term (f k)).M (X.term (f l)).M ∞,
                      Ψ (X.term (f k)).basepoint = (X.term (f l)).basepoint ∧
                      Nonempty (PartialDiffeomorphMetricApproximation
                        (riemannianClosedBallOf ((X.term (f k)).S.base.metric 0)
                          (X.term (f k)).basepoint r)
                        eta p Ψ ((X.term (f k)).S.base.metric 0)
                          ((X.term (f l)).S.base.metric 0)) := by
  obtain ⟨epsStar, hepsStar, hcompare⟩ :=
    exists_terminal_bidirectional_pairwise_metric_approximation_within_radius hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X rho hrho hinner
  obtain ⟨f, hf, hpair⟩ := hcompare eps heps hle sigma hsigma Phi hPhi X rho hrho hinner
  refine ⟨f, hf, ?_⟩
  intro r hr hrrho eta heta heta1 p
  obtain ⟨N, hN⟩ := hpair r hr hrrho eta heta heta1 p
  refine ⟨N, fun k l hk hl => ?_⟩
  obtain ⟨Ψ, hbase, hfwd, _⟩ := hN k l hk hl
  exact ⟨Ψ, hbase, hfwd⟩

theorem exists_terminal_pairwise_metric_approximation_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
              ∃ F : FiniteControlledRadius (X.reindex f hf),
                ∀ r : ℝ, 0 < r → r < F.radius → ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ p : ℕ,
                  ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
                    ∃ Ψ : PartialDiffeomorph I3 I3 (X.term (f k)).M (X.term (f l)).M ∞,
                      Ψ (X.term (f k)).basepoint = (X.term (f l)).basepoint ∧
                      Nonempty (PartialDiffeomorphMetricApproximation
                        (riemannianClosedBallOf ((X.term (f k)).S.base.metric 0)
                          (X.term (f k)).basepoint r)
                        eta p Ψ ((X.term (f k)).S.base.metric 0)
                          ((X.term (f l)).S.base.metric 0)) := by
  obtain ⟨e₁, he₁, hpairs⟩ := exists_terminal_pairwise_metric_approximation_within_radius hkappa
  obtain ⟨e₂, r₀, he₂, hr₀, hsmall⟩ := exists_curvDerivNorm_bound_on_terminal_ball hkappa
  refine ⟨min e₁ e₂, lt_min he₁ he₂, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨C, _, hc⟩ := hsmall eps heps (hle.trans (min_le_right _ _))
    sigma hsigma Phi hPhi X 0
  have hbounded : CurvatureBoundedWithin X r₀ := by
    refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * C, fun i y hy => ?_⟩
    have hj := hc i y hy.le
    change Real.sqrt (Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) y 4
      (metricRm04 ((X.term i).S.base.metric 0) y)) ≤ C at hj
    rw [metricRm04_apply] at hj
    exact (le_abs_self _).trans ((scalar_abs_le_rm (I := I3)
      ((X.term i).S.base.metric 0) y).trans
        (mul_le_mul_of_nonneg_left hj (by positivity)))
  obtain ⟨f, hf, ⟨F⟩⟩ := exists_reindex_nonempty_finiteControlledRadius_of_subsequenceCurvatureEscape
    (subsequenceCurvatureEscape_of_positiveDistanceCurvatureEscape X
      (positiveDistanceCurvatureEscape_of_curvatureBoundedWithin X hnot hr₀ hbounded))
  obtain ⟨g, hg, hp⟩ := hpairs eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi
    (X.reindex f hf) F.radius F.radius_pos F.inner_bound
  let F' : FiniteControlledRadius (X.reindex (f ∘ g) (hf.comp hg)) :=
    { radius := F.radius
      radius_pos := F.radius_pos
      inner_bound := fun r hr hrrho => by
        obtain ⟨A, hA⟩ := F.inner_bound r hr hrrho
        exact ⟨A, fun i y hy => hA (g i) y hy⟩
      points := fun i => F.points (g i)
      distance_limit := F.distance_limit.comp hg.tendsto_atTop
      curvature_limit := F.curvature_limit.comp hg.tendsto_atTop }
  exact ⟨f ∘ g, hf.comp hg, F', hp⟩

theorem exists_terminal_pointed_convergence_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
              ∃ F : FiniteControlledRadius (X.reindex f hf), ∃ r : ℕ → ℝ,
                (∀ k, 0 < r k ∧ r k < F.radius) ∧ Tendsto r atTop (nhds F.radius) ∧
                ∃ L : PointedRiemannianManifold.{u, 0, 0} (I := I3),
                ∃ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
                  ∃ C : PointedRiemannianConverges (X.toFlowSequence.atTime 0) L f maps,
                  (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
                  (∀ k, maps.target k = riemannianBallOf ((X.term (f k)).S.base.metric 0)
                    (X.term (f k)).basepoint (r k)) ∧
                  (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
                    ∀ x ∈ maps.source k, ∀ v : TangentSpace I3 x,
                      (1 - eta) * L.metric.inner x v v ≤
                        ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ∧
                      ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ≤
                        (1 + eta) * L.metric.inner x v v) ∧
                  (∀ R : ℝ, 0 ≤ R → R < F.radius →
                    IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) ∧
                  metricScalarAt L.metric L.basepoint = 1 ∧
                  ∀ (x : L.M) (v w : TangentSpace I3 x),
                    0 ≤ metricRm04StandardAt L.metric x v w w v := by
  obtain ⟨epsStar, hepsStar, hpairs⟩ :=
    exists_terminal_pairwise_metric_approximation_of_not_boundedAtDistance hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, hp⟩ := hpairs eps heps hle sigma hsigma Phi hPhi X hnot
  let Y := (X.toFlowSequence.atTime 0).subseq f
  have hcomplete : SeqMetricComplete Y := by
    constructor
    intro k
    apply X.complete (f k) 0
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (f k)], le_rfl⟩
  let P : ∀ k, ProperMetricOn (Y.obj k) := fun k =>
    properMetricOn (Y.obj k) (hcomplete.complete k) (X.connected (f k))
  obtain ⟨g, hg, r, hr, hrT, L, maps, C, hcanonical, htargets, hmetrics⟩ :=
    exists_pointed_convergence_within_radius (I := I3) P F.radius_pos (by
      intro r hr hrrho eta heta heta1 p
      obtain ⟨N, hN⟩ := hp r hr hrrho eta heta heta1 p
      refine ⟨N, fun k l hk hl => ?_⟩
      let : MetricSpace (X.term (f k)).M := (P k).ms
      let : MetricSpace (X.term (f l)).M := (P l).ms
      let : MetricSpace (Y.obj k).M := (P k).ms
      let : MetricSpace (Y.obj l).M := (P l).ms
      obtain ⟨Ψ, hbase, ⟨D⟩⟩ := hN k l hk hl
      refine ⟨Ψ, hbase, ⟨D.mono ?_ le_rfl heta1⟩⟩
      intro y hy
      change riemannianEDistOf ((Y.obj k).metric) (Y.obj k).basepoint y ≤ ENNReal.ofReal r
      have hreal : riemannianEDistOf (Y.obj k).metric (Y.obj k).basepoint y =
          ENNReal.ofReal (dist (Y.obj k).basepoint y) := (P k).realizes _ _
      rw [hreal]
      apply ENNReal.ofReal_le_ofReal
      change dist y (Y.obj k).basepoint ≤ r at hy
      with_unfolding_all exact (dist_comm (Y.obj k).basepoint y).le.trans hy)
  let F' : FiniteControlledRadius (X.reindex (f ∘ g) (hf.comp hg)) :=
    { radius := F.radius
      radius_pos := F.radius_pos
      inner_bound := fun r hr hrrho => by
        obtain ⟨A, hA⟩ := F.inner_bound r hr hrrho
        exact ⟨A, fun i y hy => hA (g i) y hy⟩
      points := fun i => F.points (g i)
      distance_limit := F.distance_limit.comp hg.tendsto_atTop
      curvature_limit := F.curvature_limit.comp hg.tendsto_atTop }
  refine ⟨f ∘ g, hf.comp hg, F', r, hr, hrT, L, maps.ofSeqSubseq f, C.ofSeqSubseq f, ?_, ?_, hmetrics, ?_, ?_, ?_⟩
  · intro k
    change (C.metrics.domain k).ofSeqSubseq f k = _
    rw [hcanonical k]
    rfl
  · intro k
    let : MetricSpace (Y.obj (g k)).M := (P (g k)).ms
    change maps.target k = riemannianBallOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint (r k)
    rw [htargets k]
    ext y
    change dist y (Y.obj (g k)).basepoint < r k ↔
      riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y < ENNReal.ofReal (r k)
    have hreal : riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y =
        ENNReal.ofReal (dist (Y.obj (g k)).basepoint y) := (P (g k)).realizes _ _
    rw [hreal, ENNReal.ofReal_lt_ofReal_iff (hr k).1, dist_comm]
  · intro R hR hRrho
    apply maps.isCompact_closed_ball_of_target_coverage (fun k => P (g k))
      (rho := F.radius) ?_ ?_ hR hRrho
    · intro S hS hSrho
      filter_upwards [hrT.eventually_const_lt hSrho] with k hk
      let : MetricSpace (Y.obj (g k)).M := (P (g k)).ms
      rw [htargets k]
      intro y hy
      have hreal : riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y =
          ENNReal.ofReal (dist (Y.obj (g k)).basepoint y) := (P (g k)).realizes _ _
      change riemannianEDistOf (Y.obj (g k)).metric (Y.obj (g k)).basepoint y ≤
        ENNReal.ofReal S at hy
      rw [hreal, ENNReal.ofReal_le_ofReal_iff hS.le] at hy
      change dist y (Y.obj (g k)).basepoint < r k
      rw [dist_comm]
      exact hy.trans_lt hk
    · intro eta heta
      obtain ⟨N, hN⟩ := hmetrics eta heta
      filter_upwards [eventually_ge_atTop N] with k hk
      exact fun x hx v => (hN k hk x hx v).2
  · apply KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains C.metrics hcanonical
    intro k
    exact X.base_one (f (g k))
  · apply sectional_nonnegative_of_pointed_admissible_pinching C.metrics hcanonical hPhi
      (fun i => X.scale (f i)) (fun i => X.scale_pos (f i))
      ((X.scale_tendsto.comp hf.tendsto_atTop).comp hg.tendsto_atTop)
    intro i y
    apply X.pinching (f i) 0 ?_ y
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (f i)], le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
