import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold

universe u

section Transfer

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ M] [IsManifold I3 ∞ N] [T2Space M] [T2Space N] [SigmaCompactSpace N]

private local instance comparisonTransferSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance comparisonTransferModelC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem MetricComparisonOn.rmNormSq_image_le_of_rmNormSq_le
    (g₀ : SmoothRiemannianMetric I3 N) (hcomplete : RiemannianMetricComplete g₀)
    (p : N) {R : ℝ} (hR : 0 < R)
    {h : ℝ → SmoothRiemannianMetric I3 N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : PartialDiffeomorph I3 I3 N M ∞} {times : Set ℝ} {order : ℕ} {eps K : ℝ}
    (C : MetricComparisonOn h g F (riemannianClosedBallOf g₀ p R) times order eps)
    (heps : 0 ≤ eps) (heps10 : eps ≤ 1 / 10) (hepsK : 40 * eps ≤ K) (horder : 2 ≤ order)
    {s : ℝ} (hs : s ∈ times) {y : N} (hysrc : y ∈ F.source)
    (hy : y ∈ riemannianClosedBallOf g₀ p R)
    (hrm : normSq0S (h s) y 4 (metricRm04At (h s) y) ≤ K ^ 2) :
    normSq0S (g s) (F y) 4 (metricRm04At (g s) (F y)) ≤ 324 * K ^ 2 := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have heps1 : eps < 1 := by linarith
  have hK : 0 ≤ K := by linarith
  let y' : sourceOpen F := ⟨y, hysrc⟩
  let : SigmaCompactSpace (sourceOpen F) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (sourceOpen F).isOpen)
  have hmodelnorm : normSq0S (witnessModelMetric F h s) y' 4
      (metricRm04At (witnessModelMetric F h s) y') ≤ K ^ 2 := by
    rw [witnessModelMetric, rmNormSq_restrictOpen (h s) (sourceOpen F) y']
    exact hrm
  have hKb : ∀ a b c : TangentSpace I3 y',
      (witnessModelMetric F h s).inner y'
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y' a b c)
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y' a b c) ≤
        K ^ 2 * (witnessModelMetric F h s).inner y' a a *
          (witnessModelMetric F h s).inner y' b b * (witnessModelMetric F h s).inner y' c c :=
    fun a b c => riemannOp_normSq_le_of_rmNormSq_le (witnessModelMetric F h s) y' hmodelnorm a b c
  let Cop := witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt (K ^ 2))
  have hT2 : ∀ a b c : TangentSpace I3 y',
      Real.sqrt ((witnessPullbackMetric F g s).inner y'
        (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y' a b c)
        (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y' a b c)) ≤
        Cop * Real.sqrt ((witnessPullbackMetric F g s).inner y' a a) *
          Real.sqrt ((witnessPullbackMetric F g s).inner y' b b) *
          Real.sqrt ((witnessPullbackMetric F g s).inner y' c c) := by
    intro a b c
    exact C.riemannOp_norm_le g₀ hcomplete p hR heps heps1 horder hs hy (sq_nonneg K) hKb a b c
  have hL1 := one_le_witnessLambda heps heps1
  have hL : witnessLambda eps ≤ 10 / 9 := by
    have hpos : 0 < 1 - eps := by linarith
    rw [witnessLambda, inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hRC := witnessRiemannC_le heps (by linarith)
  have hRC0 := witnessRiemannC_nonneg heps heps1
  have hLsq : witnessLambda eps ^ 2 ≤ 100 / 81 := by nlinarith
  have hsum : witnessRiemannC eps + Real.sqrt (K ^ 2) ≤ 3 / 2 * K := by
    rw [Real.sqrt_sq hK]
    linarith
  have hCop0 : 0 ≤ Cop := mul_nonneg (sq_nonneg _) (add_nonneg hRC0 (Real.sqrt_nonneg _))
  have hCople : Cop ≤ 2 * K := by
    have hstep := mul_le_mul hLsq hsum (add_nonneg hRC0 (Real.sqrt_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 100 / 81)
    change witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt (K ^ 2)) ≤ 2 * K
    nlinarith
  have hpull := rmNormSq_le_of_riemannOp_norm_le (witnessPullbackMetric F g s) y' hCop0 hT2
  have hnat : normSq0S (witnessPullbackMetric F g s) y' 4
      (metricRm04At (witnessPullbackMetric F g s) y') =
      normSq0S (g s) (F y) 4 (metricRm04At (g s) (F y)) := by
    rw [witnessPullbackMetric, rmNormSq_openPullbackMetric F (sourceOpen F)
      (sourceOpen_subset F) (g s) y']
  rw [hnat] at hpull
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hpull
  have hsq : Cop ^ 2 ≤ (2 * K) ^ 2 := pow_le_pow_left₀ hCop0 hCople 2
  refine hpull.trans ?_
  have h81 : ((3 : ℕ) : ℝ) ^ 4 = 81 := by norm_num
  rw [h81]
  nlinarith

end Transfer

section Limit

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem ConvergesOn.isKappaNoncollapsed_of_isParabolicallyRmControlled
    {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (X.atTime 0) P f}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.M) D}
    (hconv : ConvergesOn F S) {time : D.FlowTime}
    (hcomplete : RiemannianMetricComplete (S.base.metric time))
    (B : FlowMetricBall S time) (hB : B.IsParabolicallyRmControlled) {kappa : ℝ}
    (hseq : ∀ᶠ i in atTop,
      ParabolicallyKappaNoncollapsedBelowScale (X.term (f i)).S kappa (B.radius / 5)) :
    B.IsKappaNoncollapsed (kappa / 250) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  set t : ℝ := (time : ℝ)
  set r : ℝ := B.radius
  set p : P.M := B.center
  have hr : 0 < r := B.radius_pos
  have hcpt : ∀ ρ : ℝ, IsCompact (riemannianClosedBallOf (S.base.metric t) p ρ) :=
    fun ρ => RiemannianMetricComplete.closedEBall_isCompact hcomplete p ρ
  set eps : ℝ := min (1 / 10) (1 / (40 * r ^ 2))
  have hr2 : 0 < r ^ 2 := by positivity
  have heps : 0 < eps := lt_min (by norm_num) (by positivity)
  have heps10 : eps ≤ 1 / 10 := min_le_left _ _
  have hepsK : 40 * eps ≤ 1 / r ^ 2 := by
    have h1 : eps ≤ 1 / (40 * r ^ 2) := min_le_right _ _
    have h2 : 40 * (1 / (40 * r ^ 2)) = 1 / r ^ 2 := by field_simp
    linarith
  have hev := hconv (riemannianClosedBallOf (S.base.metric t) p r) (hcpt r) (t - r ^ 2) t
    (by linarith) hB.1 2 eps heps
  obtain ⟨i, ⟨hwin, hsrc, ⟨C⟩⟩, hk⟩ := (hev.and hseq).exists
  have httimes : t ∈ Icc (t - r ^ 2) t := ⟨by linarith, le_rfl⟩
  have hti : t ∈ (X.interval (f i)).carrier := hwin httimes
  let G := F.partialDiffeomorph i
  let τ : (X.interval (f i)).FlowTime := ⟨t, hti⟩
  let Bi : FlowMetricBall (X.term (f i)).S τ := ⟨G p, r / 5, by positivity⟩
  have hsmall : riemannianClosedBallOf (S.base.metric t) p (r / 4) ⊆
      riemannianClosedBallOf (S.base.metric t) p r :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  have hsmallB : riemannianClosedBallOf (S.base.metric t) p (r / 4) ⊆ B.set := by
    intro y hy
    change riemannianEDistOf (S.base.metric t) p y < ENNReal.ofReal r
    exact lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  have hcap : riemannianBallOf ((X.term (f i)).S.base.metric t) (G p) (r / 5) ⊆
      (G : P.M → (X.term (f i)).M) '' riemannianClosedBallOf (S.base.metric t) p (r / 4) := by
    have hcap := ball_subset_image_of_metric_lower_crossModel (S.base.metric t)
      ((X.term (f i)).S.base.metric t) G p (R := r / 4) (L := 5 / 4) (by positivity)
      (by norm_num) (hcpt _) (hsmall.trans hsrc) (by
        intro y hy v
        have hy' := hsmall hy
        have he := (C.equivalence t httimes y hy' v).1
        rw [C.pullback_eq t y hy' (fun _ => v)] at he
        have h0 := inner_self_nonneg (S.base.metric t) y v
        change (1 - eps) * (S.base.metric t).inner y v v ≤ _ at he
        nlinarith)
    have hrad : r / 4 / (5 / 4) = r / 5 := by ring
    rwa [hrad] at hcap
  have hsub : Icc (t - (r / 5) ^ 2) t ⊆ Icc (t - r ^ 2) t := by
    intro s hs
    exact ⟨by nlinarith [hs.1], hs.2⟩
  have hBi : Bi.IsParabolicallyRmControlled := by
    refine ⟨fun s hs => hwin (hsub hs), fun s hs z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hcap hz
    have hyr := hsmall hy
    have hlim := hB.2 s (hsub hs) y (hsmallB hy)
    have hrm : normSq0S (S.base.metric s) y 4 (metricRm04At (S.base.metric s) y) ≤
        (1 / r ^ 2) ^ 2 := by
      have hr4 : 0 < r ^ 4 := by positivity
      have hval : (1 / r ^ 2) ^ 2 = 1 / r ^ 4 := by ring
      rw [hval, le_div_iff₀ hr4]
      change r ^ 4 * normSq0S (S.base.metric s) y 4 (metricRm04At (S.base.metric s) y) ≤ 1
        at hlim
      linarith
    have htr := C.rmNormSq_image_le_of_rmNormSq_le (S.base.metric t) hcomplete p hr heps.le
      heps10 hepsK le_rfl (hsub hs) (hsrc hyr) hyr hrm
    change (r / 5) ^ 4 * normSq0S ((X.term (f i)).S.base.metric s) (G y) 4
      (metricRm04At ((X.term (f i)).S.base.metric s) (G y)) ≤ 1
    have hnn := normSq0S_nonneg ((X.term (f i)).S.base.metric s) (G y) 4
      (metricRm04At ((X.term (f i)).S.base.metric s) (G y))
    have hval : (r / 5) ^ 4 * (324 * (1 / r ^ 2) ^ 2) = 324 / 625 := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_left htr (by positivity : (0 : ℝ) ≤ (r / 5) ^ 4)
    linarith
  obtain ⟨hkpos, hvol⟩ := hk.2 τ Bi le_rfl hBi
  refine ⟨by positivity, ?_⟩
  have hV : IsOpen (riemannianBallOf (S.base.metric t) p r) :=
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist (S.base.metric t) p)
      continuous_const
  have hballsub : riemannianBallOf (S.base.metric t) p r ⊆
      riemannianClosedBallOf (S.base.metric t) p r := fun y hy =>
    show riemannianEDistOf (S.base.metric t) p y ≤ ENNReal.ofReal r from le_of_lt hy
  have hKV : riemannianClosedBallOf (S.base.metric t) p (r / 4) ⊆
      riemannianBallOf (S.base.metric t) p r := hsmallB
  have himg := MetricComparisonOn.volume_image_le G C httimes heps.le (by linarith) hV hballsub
    (hballsub.trans hsrc) (hcpt _) hKV
  have hsqrt : Real.sqrt ((1 + eps) ^ Module.finrank ℝ ThreeSpace) ≤ 2 := by
    rw [hdim, Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have h1 : 1 + eps ≤ 11 / 10 := by linarith
    have h2 : (1 + eps) ^ 3 ≤ (11 / 10) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
    nlinarith
  have hBvol : B.volume = riemannianVolumeMeasure I3 P.M (S.base.metric t)
      (riemannianBallOf (S.base.metric t) p r) := rfl
  have hBivol : Bi.volume = riemannianVolumeMeasure I3 (X.term (f i)).M
      ((X.term (f i)).S.base.metric t)
      (riemannianBallOf ((X.term (f i)).S.base.metric t) (G p) (r / 5)) := rfl
  have hchain : ENNReal.ofReal kappa * ENNReal.ofReal (r / 5) ^ 3 ≤
      ENNReal.ofReal 2 * B.volume := by
    rw [hBvol]
    calc ENNReal.ofReal kappa * ENNReal.ofReal (r / 5) ^ 3 ≤ Bi.volume := by
          simpa only [hdim] using hvol
      _ ≤ riemannianVolumeMeasure I3 (X.term (f i)).M ((X.term (f i)).S.base.metric t)
          ((G : P.M → (X.term (f i)).M) '' riemannianClosedBallOf (S.base.metric t) p (r / 4)) :=
          hBivol ▸ MeasureTheory.measure_mono hcap
      _ ≤ ENNReal.ofReal (Real.sqrt ((1 + eps) ^ Module.finrank ℝ ThreeSpace)) *
          riemannianVolumeMeasure I3 P.M (S.base.metric t)
            (riemannianClosedBallOf (S.base.metric t) p (r / 4)) := himg
      _ ≤ ENNReal.ofReal 2 * riemannianVolumeMeasure I3 P.M (S.base.metric t)
            (riemannianBallOf (S.base.metric t) p r) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hsqrt) (MeasureTheory.measure_mono hKV)
  have heq : ENNReal.ofReal kappa * ENNReal.ofReal (r / 5) ^ 3 =
      ENNReal.ofReal 2 * (ENNReal.ofReal (kappa / 250) * ENNReal.ofReal r ^ 3) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul hkpos.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [heq] at hchain
  rw [hdim]
  exact (ENNReal.mul_le_mul_iff_right (by simp) ENNReal.ofReal_ne_top).mp hchain

theorem ConvergesOn.parabolicallyKappaNoncollapsedBelowScale
    {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    {F : PointedRiemannianConvergenceMaps (X.atTime 0) P f}
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.M) D}
    (hconv : ConvergesOn F S)
    (hcomplete : ∀ t ∈ D.carrier, RiemannianMetricComplete (S.base.metric t))
    (hf : StrictMono f) {radii : ℕ → ℝ} (hradii : Tendsto radii atTop atTop) {kappa : ℝ}
    (hseq : ∀ i, ParabolicallyKappaNoncollapsedBelowScale (X.term i).S kappa (radii i))
    {rho : ℝ} (hrho : 0 < rho) :
    ParabolicallyKappaNoncollapsedBelowScale S (kappa / 250) rho := by
  refine ⟨hrho, fun time B _ hB => ?_⟩
  refine hconv.isKappaNoncollapsed_of_isParabolicallyRmControlled
    (hcomplete time time.property) B hB ?_
  filter_upwards [(hradii.comp hf.tendsto_atTop).eventually_ge_atTop (B.radius / 5)]
    with i hi
  exact ⟨div_pos B.radius_pos (by norm_num), fun t' B' hr' hB' =>
    (hseq (f i)).2 t' B' (hr'.trans hi) hB'⟩

end Limit

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
