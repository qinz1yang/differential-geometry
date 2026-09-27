import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.MetricConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction

import DifferentialGeometry.Geometry.Metric.Distance.LocalCompletion
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.MetricLocality
import DifferentialGeometry.Geometry.Measure.BallMetricLocality
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.Local
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_finite_pointed_metric_convergence_of_local_metric_agreement
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (g₀ : ∀ k, SmoothRiemannianMetric I (X.obj k).M)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η)
    (hmetric : ∀ᶠ k in atTop, ∀ y ∈ riemannianBallOf
      (X.obj k).metric (X.obj k).basepoint R,
      (g₀ k).inner y = (X.obj k).metric.inner y) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Q : Type uE, ∃ top : TopologicalSpace Q, letI := top
      ∃ charts : ChartedSpace E Q, letI := charts
      ∃ hman : IsManifold (modelWithCornersSelf ℝ E) ∞ Q, letI := hman
      ∃ hT2 : T2Space Q, letI := hT2
      ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
      ∃ (gQ : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) Q)
        (V : TopologicalSpace.Opens Q) (q : Q)
        (Φ : ∀ k, PartialDiffeomorph (modelWithCornersSelf ℝ E) I Q
          (X.obj (phi k)).M ∞)
        (G : ℕ → SmoothRiemannianMetric (modelWithCornersSelf ℝ E) V),
        IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
        (∀ k, closure (V : Set Q) ⊆ (Φ k).source) ∧
        (∀ k, Φ k q = (X.obj (phi k)).basepoint) ∧
        (∀ k, riemannianClosedBallOf (X.obj (phi k)).metric
          (X.obj (phi k)).basepoint r ⊆ (Φ k) '' (V : Set Q)) ∧
        (∀ k, (Φ k) '' closure (V : Set Q) ⊆
          riemannianBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint R) ∧
        (∀ k (x : V) (v w : TangentSpace (modelWithCornersSelf ℝ E) x),
          (G k).inner x v w = (g₀ (phi k)).inner (Φ k x)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) v)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  classical
  obtain ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, U, q, F, G,
    hV, hVU, hq, hG, hconv, hPhi⟩ :=
    exists_finite_pointed_metric_comparison_of_local_curvature_injectivity
      X hcomplete hconn hr hrR hη hjets hinj
  let _ := top
  let _ := charts
  let _ := hman
  let _ := hT2
  let _ := hsecond
  let _ : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace E Q
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let _ : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hVU' : V ≤ U := subset_closure.trans hVU
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hPhi.and hG).and
    (hphi.tendsto_atTop.eventually hmetric))
  let f : ℕ → ℕ := fun k => phi (k + N)
  have hadd : StrictMono (fun k : ℕ => k + N) :=
    fun _ _ h => Nat.add_lt_add_right h N
  have hf : StrictMono f := hphi.comp hadd
  choose Ψ hsource hEq hbase hcapture hupper using
    fun k => (hN (k + N) (by omega)).1.1
  let GV : ℕ → SmoothRiemannianMetric (modelWithCornersSelf ℝ E) V :=
    fun k => (G (k + N)).restrictOpenOfSubset hVU'
  refine ⟨f, hf, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Ψ, GV,
    hV, hq, ?_, hbase, hcapture, hupper, ?_, ?_⟩
  · intro k
    exact hVU.trans (subset_closure.trans (hsource k))
  · intro k x v w
    have hsrc : (x : Q) ∈ (Ψ k).source :=
      hsource k (subset_closure (hVU' x.property))
    have hnear : (Ψ k : Q → (X.obj (f k)).M) =ᶠ[𝓝 (x : Q)] F (k + N) :=
      Filter.eventuallyEq_of_mem ((Ψ k).open_source.mem_nhds hsrc) (hEq k)
    have hderiv := hnear.mfderiv_eq
      (I := modelWithCornersSelf ℝ E) (I' := I)
    have himage : Ψ k x ∈ riemannianBallOf (X.obj (f k)).metric
        (X.obj (f k)).basepoint R := hupper k ⟨x, subset_closure x.property, rfl⟩
    have hmet := (hN (k + N) (by omega)).2 (Ψ k x) himage
    change (G (k + N)).inner ⟨x, hVU' x.property⟩ v w = _
    rw [hmet, hnear.self_of_nhds, hderiv]
    exact (hN (k + N) (by omega)).1.2 ⟨x, hVU' x.property⟩ v w
  · have hc := (hconv.comp_subseq hadd).restrictOpenOfSubset hVU'
    have he : (gQ.restrictOpen U).restrictOpenOfSubset hVU' = gQ.restrictOpen V := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rfl
    rw [he] at hc
    exact hc


open _root_.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped ENNReal

private theorem exists_uniform_injectivity_of_complete_metric_extension
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ iota : ℝ, 0 < iota ∧
      ∀ (P : PointedRiemannianManifold.{u, uE, uH} I)
        (g' : SmoothRiemannianMetric I P.M) (U : Set P.M),
        RiemannianMetricComplete g' → IsOpen U →
        ∀ {r a R C : ℝ}, 0 ≤ r → 0 < a → r + a ≤ R → a ^ 4 * C ^ 2 ≤ 1 →
          riemannianClosedBallOf P.metric P.basepoint R ⊆ U →
          (∀ z ∈ U, g'.inner z = P.metric.inner z) →
          (∀ z (v : TangentSpace I z), P.metric.inner z v v ≤ g'.inner z v v) →
          (∀ z ∈ riemannianClosedBallOf P.metric P.basepoint R,
            curvDerivNorm 0 P.metric z ≤ C) →
          (∀ x ∈ riemannianClosedBallOf P.metric P.basepoint r,
            ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
              riemannianVolumeMeasure I P.M P.metric (riemannianBallOf P.metric x a)) →
          ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint r,
            HasInjRadiusAt { P with metric := g' } x (iota * a) := by
  obtain ⟨iota, hiota, hinj⟩ :=
    PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.local_metric_injectivity
      (I := I) hκ
  refine ⟨iota, hiota, ?_⟩
  intro P g' U hcomplete hU r a R C hr ha hra hac hRU hsame hmono hcurv hvol x hx
  have heq : ∀ z ∈ riemannianClosedBallOf P.metric P.basepoint R,
      g'.inner z = P.metric.inner z := fun z hz => hsame z (hRU hz)
  have hvol' : ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
      riemannianVolumeMeasure I P.M g' (riemannianBallOf g' x a) := by
    rw [Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall
      P.metric g' hr ha.le hra hx heq hmono]
    exact hvol x hx
  have hcontrol : ∀ y ∈ riemannianBallOf g' x a,
      a ^ 4 * Tensor0SBundle.normSq0S g' y 4 (metricRm04At g' y) ≤ 1 := by
    intro y hy
    rw [riemannianBallOf_eq_of_eqOn_outer_closedBall
      P.metric g' hr ha.le hra hx heq hmono] at hy
    have hyR : y ∈ riemannianClosedBallOf P.metric P.basepoint R :=
      riemannianClosedBallOf_subset_of_add_radius_le P.metric hr ha.le hra hx
        (show riemannianEDistOf P.metric x y ≤ ENNReal.ofReal a from le_of_lt hy)
    have hgerm : ∀ᶠ z in 𝓝 y, ∀ v w : TangentSpace I z,
        g'.inner z v w = P.metric.inner z v w := by
      filter_upwards [hU.mem_nhds (hRU hyR)] with z hz
      intro v w
      exact congrArg (fun A => A v w) (hsame z hz)
    have hbound : curvDerivNorm 0 g' y ≤ C := by
      rw [curvDerivNorm_eq_of_metric_eventuallyEq g' P.metric y hgerm 0]
      exact hcurv y hyR
    have hsq : Tensor0SBundle.normSq0S g' y 4 (metricRm04At g' y) ≤ C ^ 2 := by
      change Real.sqrt (Tensor0SBundle.normSq0S g' y 4 (metricRm04At g' y)) ≤ C at hbound
      have hC : 0 ≤ C := (Real.sqrt_nonneg _).trans hbound
      have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hC).2 hbound
      rwa [Real.sq_sqrt (Tensor0SBundle.normSq0S_nonneg _ _ _ _)] at h
    exact (mul_le_mul_of_nonneg_left hsq (pow_nonneg ha.le 4)).trans hac
  exact hasInjRadiusAt_of_expMap_injOn { P with metric := g' } x (mul_pos hiota ha)
    (hinj P.M g' hcomplete x a ha hcontrol hvol')


private theorem exists_finite_pointed_metric_convergence_of_all_compact_balls
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R₀ R r a κ C₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hRR₀ : R < R₀)
    (ha : 0 < a) (hra : r + a ≤ R) (hκ : 0 < κ)
    (hac : a ^ 4 * C₀ ^ 2 ≤ 1)
    (hcompact : ∀ k, IsCompact (riemannianClosedBallOf
      (X.obj k).metric (X.obj k).basepoint R₀))
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hcurv : ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
      (X.obj k) (X.obj k).basepoint R 0 C₀)
    (hvol : ∀ᶠ k in atTop, ∀ x ∈ riemannianClosedBallOf
        (X.obj k).metric (X.obj k).basepoint r,
      ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure I (X.obj k).M (X.obj k).metric
          (riemannianBallOf (X.obj k).metric x a)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Q : Type uE, ∃ top : TopologicalSpace Q, letI := top
      ∃ charts : ChartedSpace E Q, letI := charts
      ∃ hman : IsManifold (modelWithCornersSelf ℝ E) ∞ Q, letI := hman
      ∃ hT2 : T2Space Q, letI := hT2
      ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
      ∃ (gQ : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) Q)
        (V : TopologicalSpace.Opens Q) (q : Q)
        (Φ : ∀ k, PartialDiffeomorph (modelWithCornersSelf ℝ E) I Q
          (X.obj (phi k)).M ∞)
        (G : ℕ → SmoothRiemannianMetric (modelWithCornersSelf ℝ E) V),
        IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
        (∀ k, closure (V : Set Q) ⊆ (Φ k).source) ∧
        (∀ k, Φ k q = (X.obj (phi k)).basepoint) ∧
        (∀ k, riemannianClosedBallOf (X.obj (phi k)).metric
          (X.obj (phi k)).basepoint r ⊆ (Φ k) '' (V : Set Q)) ∧
        (∀ k, (Φ k) '' closure (V : Set Q) ⊆
          riemannianBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint R) ∧
        (∀ k (x : V) (v w : TangentSpace (modelWithCornersSelf ℝ E) x),
          (G k).inner x v w = (X.obj (phi k)).metric.inner (Φ k x)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) v)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  classical
  choose g U hcomplete hU hKU hsame hmono hdist hopen hclosed hpairs using fun k =>
    Geometry.exists_complete_metric_extension_of_riemannianClosedBall
      (X.obj k).metric (X.obj k).basepoint (hcompact k)
  let Y : PointedRiemannianSeq.{u, uE, uH} I :=
    { obj := fun k => { X.obj k with metric := g k } }
  have hcompleteY : SeqMetricComplete Y := ⟨fun k => (hcomplete k).complete⟩
  have hjetsY : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (Y.obj k) (Y.obj k).basepoint R p C := by
    intro p
    obtain ⟨C, hC, hbound⟩ := hjets p
    refine ⟨C, hC, hbound.mono fun k hk x hx => ?_⟩
    have hxg : x ∈ riemannianClosedBallOf (X.obj k).metric (X.obj k).basepoint R := by
      change x ∈ riemannianClosedBallOf (g k) (X.obj k).basepoint R at hx
      rwa [hclosed k R (hr.trans hrR.le) hRR₀] at hx
    have hxU : x ∈ U k := hKU k (riemannianClosedBallOf_mono _ _ hRR₀.le hxg)
    have hgerm : ∀ᶠ y in 𝓝 x, ∀ v w, (g k).inner y v w = (X.obj k).metric.inner y v w := by
      filter_upwards [(hU k).mem_nhds hxU] with y hy v w
      exact congrArg (fun A => A v w) (hsame k y hy)
    change curvDerivNorm p (g k) x ≤ C
    rw [curvDerivNorm_eq_of_metric_eventuallyEq (g k) (X.obj k).metric x hgerm p]
    exact hk x hxg
  obtain ⟨iota, hiota, hinj⟩ := exists_uniform_injectivity_of_complete_metric_extension.{u}
    (I := I) hκ
  have hinjY : ∀ᶠ k in atTop, ∀ x : (Y.obj k).M,
      riemannianEDistOf (Y.obj k).metric (Y.obj k).basepoint x ≤ ENNReal.ofReal r →
        HasInjRadiusAt (Y.obj k) x (iota * a) := by
    filter_upwards [hcurv, hvol] with k hk hv x hx
    have hxg : x ∈ riemannianClosedBallOf (X.obj k).metric (X.obj k).basepoint r := by
      change x ∈ riemannianClosedBallOf (g k) (X.obj k).basepoint r at hx
      rwa [hclosed k r hr (hrR.trans hRR₀)] at hx
    exact hinj (X.obj k) (g k) (U k) (hcomplete k) (hU k) hr ha hra hac
      (fun z hz => hKU k (riemannianClosedBallOf_mono _ _ hRR₀.le hz))
      (hsame k) (hmono k) hk hv x hxg
  obtain ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Φ, G,
    hV, hq, hsource, hbase, hcapture, hupper, hmetric, hconv⟩ :=
    exists_finite_pointed_metric_convergence_of_local_metric_agreement
      Y (fun k => (X.obj k).metric) hcompleteY hconn hr hrR (mul_pos hiota ha) hjetsY hinjY
      (Eventually.of_forall fun k y hy => by
        have hsmall : y ∈ riemannianBallOf (X.obj k).metric (X.obj k).basepoint R := by
          change y ∈ riemannianBallOf (g k) (X.obj k).basepoint R at hy
          rwa [hopen k R hRR₀.le] at hy
        exact (hsame k y (hKU k (hsmall.le.trans (ENNReal.ofReal_le_ofReal hRR₀.le)))).symm)
  let _ := top
  let _ := charts
  let _ := hman
  let _ := hT2
  let _ := hsecond
  refine ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Φ, G,
    hV, hq, hsource, hbase, ?_, ?_, hmetric, hconv⟩
  · intro k
    simpa only [Y, hclosed (phi k) r hr (hrR.trans hRR₀)] using hcapture k
  · intro k
    simpa only [Y, hopen (phi k) R hRR₀.le] using hupper k


theorem exists_finite_pointed_metric_convergence_of_compact_balls
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R₀ R r a κ C₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hRR₀ : R < R₀)
    (ha : 0 < a) (hra : r + a ≤ R) (hκ : 0 < κ)
    (hac : a ^ 4 * C₀ ^ 2 ≤ 1)
    (hcompact : ∀ᶠ k in atTop, IsCompact (riemannianClosedBallOf
      (X.obj k).metric (X.obj k).basepoint R₀))
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hcurv : ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
      (X.obj k) (X.obj k).basepoint R 0 C₀)
    (hvol : ∀ᶠ k in atTop, ∀ x ∈ riemannianClosedBallOf
        (X.obj k).metric (X.obj k).basepoint r,
      ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
        riemannianVolumeMeasure I (X.obj k).M (X.obj k).metric
          (riemannianBallOf (X.obj k).metric x a)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Q : Type uE, ∃ top : TopologicalSpace Q, letI := top
      ∃ charts : ChartedSpace E Q, letI := charts
      ∃ hman : IsManifold (modelWithCornersSelf ℝ E) ∞ Q, letI := hman
      ∃ hT2 : T2Space Q, letI := hT2
      ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
      ∃ (gQ : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) Q)
        (V : TopologicalSpace.Opens Q) (q : Q)
        (Φ : ∀ k, PartialDiffeomorph (modelWithCornersSelf ℝ E) I Q
          (X.obj (phi k)).M ∞)
        (G : ℕ → SmoothRiemannianMetric (modelWithCornersSelf ℝ E) V),
        IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
        (∀ k, closure (V : Set Q) ⊆ (Φ k).source) ∧
        (∀ k, Φ k q = (X.obj (phi k)).basepoint) ∧
        (∀ k, riemannianClosedBallOf (X.obj (phi k)).metric
          (X.obj (phi k)).basepoint r ⊆ (Φ k) '' (V : Set Q)) ∧
        (∀ k, (Φ k) '' closure (V : Set Q) ⊆
          riemannianBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint R) ∧
        (∀ k (x : V) (v w : TangentSpace (modelWithCornersSelf ℝ E) x),
          (G k).inner x v w = (X.obj (phi k)).metric.inner (Φ k x)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) v)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hcompact
  let shift : ℕ → ℕ := fun k => k + N
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_right h N
  have hcompact' (k) := hN (shift k) (Nat.le_add_left N k)
  have hjets' : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        ((X.subseq shift).obj k) ((X.subseq shift).obj k).basepoint R p C := by
    intro p
    obtain ⟨C, hC, hb⟩ := hjets p
    exact ⟨C, hC, hshift.tendsto_atTop.eventually hb⟩
  obtain ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Φ, G,
    hV, hq, hsource, hbase, hcapture, hupper, hmetric, hconv⟩ :=
    exists_finite_pointed_metric_convergence_of_all_compact_balls
      (X.subseq shift) (fun k => hconn (shift k)) hr hrR hRR₀ ha hra hκ hac
      hcompact' hjets' (hshift.tendsto_atTop.eventually hcurv)
      (hshift.tendsto_atTop.eventually hvol)
  exact ⟨shift ∘ phi, hshift.comp hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Φ, G,
    hV, hq, hsource, hbase, hcapture, hupper, hmetric, hconv⟩

end DifferentialGeometry.CheegerGromovCompactness
