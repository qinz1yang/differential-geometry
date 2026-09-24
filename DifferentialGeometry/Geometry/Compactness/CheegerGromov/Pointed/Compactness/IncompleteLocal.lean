import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalMetricExtension
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Local
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.LocalProperness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricAgreement
import DifferentialGeometry.Geometry.Metric.Distance.LocalCompletion
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem exists_growing_complete_extensions
    (X : PointedRiemannianSeq.{u, uE, uH} I) {rho : ℝ} (hrho : 0 < rho)
    (hcompact : ∀ R : ℝ, 0 < R → R < rho →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R)) :
    ∃ (sigma : ℕ → ℕ), StrictMono sigma ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
        ∃ (g : ∀ n, SmoothRiemannianMetric I (X.obj (sigma n)).M)
          (U : ∀ n, Set (X.obj (sigma n)).M),
          (∀ n, RiemannianMetricComplete (g n)) ∧
          (∀ n, IsOpen (U n)) ∧
          (∀ n, riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint (r n) ⊆ U n) ∧
          (∀ n, ∀ y ∈ U n, (g n).inner y = (X.obj (sigma n)).metric.inner y) ∧
          (∀ n, ∀ y (v : TangentSpace I y), (X.obj (sigma n)).metric.inner y v v ≤ (g n).inner y v v) ∧
          (∀ n, ∀ R : ℝ, R ≤ r n →
            riemannianBallOf (g n) (X.obj (sigma n)).basepoint R =
              riemannianBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint R) ∧
          (∀ n, ∀ R : ℝ, 0 ≤ R → R < r n →
            riemannianClosedBallOf (g n) (X.obj (sigma n)).basepoint R =
              riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint R) ∧
          ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ n in atTop,
            riemannianClosedBallOf (g n) (X.obj (sigma n)).basepoint R =
              riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint R ∧
            (∀ y ∈ riemannianBallOf (g n) (X.obj (sigma n)).basepoint R,
              (g n).inner y = (X.obj (sigma n)).metric.inner y) := by
  classical
  let r : ℕ → ℝ := fun n => rho - rho / ((n : ℝ) + 2)
  have hr (n) : 0 < r n ∧ r n < rho := by
    constructor
    · apply sub_pos.mpr
      exact div_lt_self hrho (by linarith [Nat.cast_nonneg (α := ℝ) n])
    · exact sub_lt_self _ (by positivity)
  have hrlim : Tendsto r atTop (𝓝 rho) := by
    have hd : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num))
        tendsto_natCast_atTop_atTop
    simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hd)
  choose N hN using fun n => eventually_atTop.mp (hcompact (r n) (hr n).1 (hr n).2)
  obtain ⟨sigma, hsigma, hsigN⟩ := exists_strictMono_ge N
  choose g U hcomplete hU hKU hsame hmono hd hopen hclosed hpairs using fun n =>
    Geometry.exists_complete_metric_extension_of_riemannianClosedBall
      (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint (hN n (sigma n) (hsigN n))
  refine ⟨sigma, hsigma, r, hr, hrlim, g, U, hcomplete, hU, hKU, hsame, hmono,
    hopen, hclosed, ?_⟩
  intro R hR hRrho
  filter_upwards [hrlim.eventually (eventually_gt_nhds hRrho)] with n hn
  refine ⟨hclosed n R hR.le hn, ?_⟩
  intro y hy
  rw [hopen n R hn.le] at hy
  exact hsame n y (hKU n (hy.le.trans (ENNReal.ofReal_le_ofReal hn.le)))


end DifferentialGeometry.CheegerGromovCompactness

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


private theorem exists_complete_extensions_with_inner_bounds
    (X : PointedRiemannianSeq.{u, uE, uH} I) {rho : ℝ} (hrho : 0 < rho)
    (hcompact : ∀ R : ℝ, 0 < R → R < rho →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R))
    (hjets : ∀ R : ℝ, 0 < R → R < rho → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p C)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∃ (sigma : ℕ → ℕ), StrictMono sigma ∧
      ∃ g : ∀ n, SmoothRiemannianMetric I (X.obj (sigma n)).M,
        let Y : PointedRiemannianSeq I := { obj := fun n => { X.obj (sigma n) with metric := g n } }
        SeqMetricComplete Y ∧
        (∀ R : ℝ, 0 < R → R < rho → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
          ∀ᶠ n in atTop, HasLocalCurvDerivBound (Y.obj n) (Y.obj n).basepoint R p C) ∧
        (∀ r : ℝ, 0 < r → r < rho → ∃ η : ℝ, 0 < η ∧
          ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint r,
            HasInjRadiusAt (I := I) (Y.obj n) x η) ∧
        ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ n in atTop,
          riemannianClosedBallOf (g n) (X.obj (sigma n)).basepoint R =
            riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint R ∧
          ∀ y ∈ riemannianBallOf (g n) (X.obj (sigma n)).basepoint R,
            (g n).inner y = (X.obj (sigma n)).metric.inner y := by
  obtain ⟨sigma, hsigma, radius, hradius, hradlim, g, U, hc, hU, hKU, heq, hmono, hopen, hclosed, hagree⟩ :=
    exists_growing_complete_extensions X hrho hcompact
  refine ⟨sigma, hsigma, g, ⟨fun n => (hc n).complete⟩, ?_, ?_, hagree⟩
  · intro R hR hRrho p
    obtain ⟨C, hC, hCbound⟩ := hjets R hR hRrho p
    refine ⟨C, hC, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hCbound,
      hradlim.eventually (eventually_gt_nhds hRrho)] with n hn hRn
    intro x hx
    have hxg : x ∈ riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint R := by
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
  · intro r hr hrrho
    let R := (r + rho) / 2
    have hrR : r < R := by dsimp [R]; linarith
    have hRrho : R < rho := by dsimp [R]; linarith
    obtain ⟨C, hC, hCbound⟩ := hjets R (hr.trans hrR) hRrho 0
    obtain ⟨a, κ, ha, hκ, hra, hac, hv⟩ := hvol r R hr hrR hRrho C hC
    obtain ⟨iota, hiota, hinj⟩ := exists_uniform_injectivity_of_complete_metric_extension.{u} (I := I) hκ
    refine ⟨iota * a, mul_pos hiota ha, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hCbound, hsigma.tendsto_atTop.eventually hv,
      hradlim.eventually (eventually_gt_nhds hRrho)] with n hn hvn hRn
    intro x hx
    have hxg : x ∈ riemannianClosedBallOf (X.obj (sigma n)).metric (X.obj (sigma n)).basepoint r := by
      change x ∈ riemannianClosedBallOf (g n) (X.obj (sigma n)).basepoint r at hx
      rwa [hclosed n r hr.le (hrR.trans hRn)] at hx
    exact hinj (X.obj (sigma n)) (g n) (U n) (hc n) (hU n) hr.le ha hra hac
      (fun z hz => hKU n (riemannianClosedBallOf_mono _ _ hRn.le hz)) (heq n) (hmono n)
      hn hvn x hxg


private theorem exists_pointed_limit_for_complete_extensions
    (X : PointedRiemannianSeq.{u, uE, uH} I) (hconn : ∀ n, ConnectedSpace (X.obj n).M)
    {rho : ℝ} (hrho : 0 < rho)
    (hcompact : ∀ R : ℝ, 0 < R → R < rho →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R))
    (hjets : ∀ R : ℝ, 0 < R → R < rho → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p C)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∃ (sigma : ℕ → ℕ), StrictMono sigma ∧
      ∃ g : ∀ n, SmoothRiemannianMetric I (X.obj (sigma n)).M,
        let Y : PointedRiemannianSeq I := { obj := fun n => { X.obj (sigma n) with metric := g n } }
        ∃ (f : ℕ → ℕ), StrictMono f ∧ ∃ (r : ℕ → ℝ),
          (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
          ∃ (L : PointedRiemannianManifold.{u, uE, uH} I)
            (F : PointedRiemannianConvergenceMaps Y L f) (C : MetricConvergenceData F),
            (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
            (∀ n, F.target n = riemannianBallOf (g (f n)) (X.obj (sigma (f n))).basepoint (r n)) ∧
            (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho) ∧
            (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) ∧
            ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ n in atTop,
              riemannianClosedBallOf (g (f n)) (X.obj (sigma (f n))).basepoint R =
                riemannianClosedBallOf (X.obj (sigma (f n))).metric (X.obj (sigma (f n))).basepoint R ∧
              ∀ y ∈ riemannianBallOf (g (f n)) (X.obj (sigma (f n))).basepoint R,
                (g (f n)).inner y = (X.obj (sigma (f n))).metric.inner y := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨sigma, hsigma, g, hc, hgjets, hginj, hagree⟩ :=
    exists_complete_extensions_with_inner_bounds X hrho hcompact hjets hvol
  let Y : PointedRiemannianSeq.{u, uE, uH} I :=
    { obj := fun n => { X.obj (sigma n) with metric := g n } }
  have hYconn (n) : ConnectedSpace (Y.obj n).M := hconn (sigma n)
  obtain ⟨phi, hphi, hpair⟩ :=
    exists_subsequence_pairwise_metric_approximation_within_radius Y hc hYconn hrho hgjets hginj
  let P : ∀ n, ProperMetricOn ((Y.subseq phi).obj n) :=
    fun n => properMetricOn (Y.obj (phi n)) (hc.complete (phi n)) (hYconn (phi n))
  have hB : ∀ r : ℝ, 0 < r → r < rho → ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ p : ℕ,
      ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
        letI : MetricSpace (Y.obj (phi k)).M := (P k).ms
        letI : MetricSpace (Y.obj (phi l)).M := (P l).ms
        ∃ Ψ : PartialDiffeomorph I I (Y.obj (phi k)).M (Y.obj (phi l)).M ∞,
          Ψ (Y.obj (phi k)).basepoint = (Y.obj (phi l)).basepoint ∧
          Nonempty (PartialDiffeomorphMetricApproximation
            (Metric.closedBall (Y.obj (phi k)).basepoint r) eps p Ψ
              (Y.obj (phi k)).metric (Y.obj (phi l)).metric) := by
    intro r hr hrrho eps heps heps1 p
    obtain ⟨N, hN⟩ := hpair r hr hrrho eps heps heps1 p
    refine ⟨N, fun k l hk hl => ?_⟩
    obtain ⟨Ψ, hbase, hmetric⟩ := hN k l hk hl
    refine ⟨Ψ, hbase, ?_⟩
    let _ : MetricSpace (Y.obj (phi k)).M := (P k).ms
    have heq : Metric.closedBall (Y.obj (phi k)).basepoint r =
        riemannianClosedBallOf (Y.obj (phi k)).metric (Y.obj (phi k)).basepoint r := by
      ext y
      have hreal := (P k).realizes (Y.obj (phi k)).basepoint y
      change riemannianEDistOf (Y.obj (phi k)).metric (Y.obj (phi k)).basepoint y =
        ENNReal.ofReal (dist (Y.obj (phi k)).basepoint y) at hreal
      change dist y (Y.obj (phi k)).basepoint ≤ r ↔
        riemannianEDistOf (Y.obj (phi k)).metric (Y.obj (phi k)).basepoint y ≤ ENNReal.ofReal r
      rw [hreal, ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
    rw [heq]
    exact hmetric
  obtain ⟨psi, hpsi, r, hr, hrlim, L, F, C, hcanonical, htarget, hradial, hbound⟩ :=
    exists_pointed_convergence_within_radius_and_radial_bound P hrho hB
  let f := phi ∘ psi
  let F' := F.ofSeqSubseq phi
  have hf : StrictMono f := hphi.comp hpsi
  have htarg (n) : F'.target n = riemannianBallOf (g (f n)) (X.obj (sigma (f n))).basepoint (r n) := by
    change F.target n = _
    rw [htarget n]
    ext y
    let metricn := (P (psi n)).ms
    let _ : MetricSpace ((Y.subseq phi).obj (psi n)).M := metricn
    have hreal := (P (psi n)).realizes ((Y.subseq phi).obj (psi n)).basepoint y
    change riemannianEDistOf (g (f n)) ((Y.subseq phi).obj (psi n)).basepoint y =
      ENNReal.ofReal (dist ((Y.subseq phi).obj (psi n)).basepoint y) at hreal
    change dist y ((Y.subseq phi).obj (psi n)).basepoint < r n ↔
      riemannianEDistOf (g (f n)) ((Y.subseq phi).obj (psi n)).basepoint y < ENNReal.ofReal (r n)
    rw [hreal, ENNReal.ofReal_lt_ofReal_iff (hr n).1, dist_comm]
  have hcpt : ∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf L.metric L.basepoint R) := by
    intro R hR hRrho
    apply F.isCompact_closed_ball_of_target_coverage (fun n => P (psi n))
      (rho := rho) ?_ ?_ hR hRrho
    · intro S hS hSrho
      filter_upwards [hrlim.eventually (eventually_gt_nhds hSrho)] with n hn
      rw [htarget n]
      intro y hy
      let metricn := (P (psi n)).ms
      let _ : MetricSpace ((Y.subseq phi).obj (psi n)).M := metricn
      have hreal := (P (psi n)).realizes ((Y.subseq phi).obj (psi n)).basepoint y
      change riemannianEDistOf (g (f n)) ((Y.subseq phi).obj (psi n)).basepoint y =
        ENNReal.ofReal (dist ((Y.subseq phi).obj (psi n)).basepoint y) at hreal
      change riemannianEDistOf (g (f n)) ((Y.subseq phi).obj (psi n)).basepoint y ≤ ENNReal.ofReal S at hy
      rw [hreal] at hy
      change dist y ((Y.subseq phi).obj (psi n)).basepoint < r n
      rw [dist_comm]
      exact ((ENNReal.ofReal_le_ofReal_iff hS.le).mp hy).trans_lt hn
    · intro eps heps
      obtain ⟨N, hN⟩ := hbound eps heps
      exact (eventually_ge_atTop N).mono fun n hn x hx v => (hN n hn x hx v).2
  refine ⟨sigma, hsigma, g, f, hf, r, hr, hrlim, L, F', C.metrics.ofSeqSubseq phi,
    ?_, htarg, hradial, hcpt, ?_⟩
  · intro n
    change MetricSourceData.ofSeqSubseq phi n (C.metrics.domain n) = _
    rw [hcanonical n]
    rfl
  · intro R hR hRrho
    exact hf.tendsto_atTop.eventually (hagree R hR hRrho)


theorem exists_pointed_convergence_of_eventually_compact_inner_balls
    (X : PointedRiemannianSeq.{u, uE, uH} I) (hconn : ∀ n, ConnectedSpace (X.obj n).M)
    {rho : ℝ} (hrho : 0 < rho)
    (hcompact : ∀ R : ℝ, 0 < R → R < rho →
      ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R))
    (hjets : ∀ R : ℝ, 0 < R → R < rho → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R p C)
    (hvol : ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure I (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (L : PointedRiemannianManifold.{u, uE, uH} I)
        (F : PointedRiemannianConvergenceMaps X L f) (C : MetricConvergenceData F),
        (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) ∧
        ∀ R : ℝ, 0 < R → R < rho → ∀ᶠ n in atTop,
          riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆ F.target n := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨sigma, hsigma, g, f, hf, r, hr, hrlim, L, F, C, hcanonical, htarget, hradial, hcpt, hagree⟩ :=
    exists_pointed_limit_for_complete_extensions X hconn hrho hcompact hjets hvol
  let Y : PointedRiemannianSeq.{u, uE, uH} I :=
    { obj := fun n => { X.obj (sigma n) with metric := g n } }
  obtain ⟨F0, hF0, C0, hC0⟩ :=
    F.exists_canonical_convergence_of_inner_ball_metric_agreement C hcanonical
      (fun n => (X.obj (sigma n)).metric) hrho hradial hcpt (by
        intro R hR hRrho
        filter_upwards [hagree R hR hRrho] with n hn
        exact fun y hy => (hn.2 y hy).symm)
  let hF : PointedRiemannianConvergenceMaps (X.subseq sigma) L f := F0
  let Fo := hF.ofSeqSubseq sigma
  let hCo : MetricConvergenceData Fo := C0.ofSeqSubseq sigma
  refine ⟨sigma ∘ f, hsigma.comp hf, L, Fo, hCo, ?_, hradial, hcpt, ?_⟩
  · intro n
    change MetricSourceData.ofSeqSubseq sigma n (C0.domain n) = _
    rw [hC0 n]
    rfl
  · intro R hR hRrho
    filter_upwards [hagree R hR hRrho, hrlim.eventually (eventually_gt_nhds hRrho)] with n hn hrn
    have htarg : Fo.target n = riemannianBallOf (g (f n)) (X.obj (sigma (f n))).basepoint (r n) := by
      change (F0.partialDiffeomorph n).target = _
      rw [hF0 n]
      exact htarget n
    rw [htarg]
    change riemannianClosedBallOf (X.obj (sigma (f n))).metric (X.obj (sigma (f n))).basepoint R ⊆ _
    rw [← hn.1]
    intro y hy
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr n).1).mpr hrn)

end DifferentialGeometry.CheegerGromovCompactness
