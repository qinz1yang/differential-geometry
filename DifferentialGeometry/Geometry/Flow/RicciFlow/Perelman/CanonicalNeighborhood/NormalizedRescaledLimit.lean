import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLocalBackwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedSourceComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedEndCurvature
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompositionComparison
import DifferentialGeometry.Geometry.Metric.Distance.Topology

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u v
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private theorem exists_connected_terminal_patch
    (P : PointedRiemannianManifold.{0, 0, 0} I3)
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := P.M) D)
    (hS : IsSolutionOn S) (hterminal : S.base.metric 0 = P.metric)
    {tau : ℝ} (hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ)
    (hscalar : metricScalarAt P.metric P.basepoint = 1) :
    let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
    ∃ U : TopologicalSpace.Opens P.M, ∃ hp : P.basepoint ∈ U,
      ∃ hpath : PathConnectedSpace U,
      let _ : PathConnectedSpace U := hpath
      let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
      let _ : PseudoMetricSpace U := (P.metric.restrictOpen U).toPseudoMetricSpace
      let _ : MetricSpace U := MetricSpace.ofT0PseudoMetricSpace U
      IsSolutionOn (solutionOnRestrictOpen S U) ∧
        (∀ t ∈ Icc (-tau) 0, SecLower ((S.base.metric t).restrictOpen U) 0 univ) ∧
        metricScalarAt ((S.base.metric 0).restrictOpen U) ⟨P.basepoint, hp⟩ = 1 ∧
        ∀ x y : U, edist x y = riemannianEDistOf ((S.base.metric 0).restrictOpen U) x y := by
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
  dsimp only
  let U : TopologicalSpace.Opens P.M := ⟨riemannianBallOf P.metric P.basepoint 1,
    isOpen_lt (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
      P.metric P.basepoint) continuous_const⟩
  have hp : P.basepoint ∈ U := by
    change riemannianEDistOf P.metric P.basepoint P.basepoint < ENNReal.ofReal 1
    rw [riemannianEDistOf_self]
    norm_num
  have hpath : PathConnectedSpace U :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_riemannianBallOf P.metric P.basepoint zero_lt_one)
  refine ⟨U, hp, hpath, ?_⟩
  let _ : PathConnectedSpace U := hpath
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let _ : PseudoMetricSpace U := (P.metric.restrictOpen U).toPseudoMetricSpace
  let _ : MetricSpace U := MetricSpace.ofT0PseudoMetricSpace U
  refine ⟨isSolutionOn_restrictOpen S hS U, ?_, ?_, ?_⟩
  · intro t ht x _ v w
    have hslots : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> rfl
    have hcurv : 0 ≤ metricRm04StandardAt (S.base.metric t) (x : P.M) v w w v := by
      erw [metricRm04StandardAt_apply]
      have hh := hsec t ht x (mem_univ _) v w
      simp only [zero_mul] at hh
      convert hh using 1
      congr 1
      funext i
      fin_cases i <;> rfl
    have hr := metricRm04StandardAt_restrictOpen (S.base.metric t) U x v w w v
    simp only [mfderiv_subtype_val_apply] at hr
    simpa only [zero_mul, ← metricRm04StandardAt_apply, hslots, hr] using hcurv
  · rw [metricScalarAt_restrictOpen, hterminal]
    exact hscalar
  · intro x y
    rw [hterminal]
    rfl


theorem exists_local_backward_limit_with_end_comparison
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N],
      ∀ H : ℕ → SmoothRiemannianMetric I3 N, ∀ x : ℕ → N,
      ∀ B : ∀ i, PartialDiffeomorph I3 I3 N (X.term i).M ∞,
      ∀ R : ℝ, 0 < R →
      (∀ i, riemannianClosedBallOf (H i) (x i) R ⊆ (B i).source) →
      (∀ i, B i (x i) = (X.term i).basepoint) →
      (∀ i, riemannianClosedBallOf ((X.term i).S.base.metric 0)
        (X.term i).basepoint (R / 4) ⊆ (B i) '' riemannianClosedBallOf (H i) (x i) R) →
      (∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
        ∀ y ∈ riemannianClosedBallOf (H i) (x i) R, ∀ v : TangentSpace I3 y,
          (1 - eta) * (H i).inner y v v ≤ ((X.term i).S.base.metric 0).inner (B i y)
            (mfderiv I3 I3 (B i) y v) (mfderiv I3 I3 (B i) y v) ∧
          ((X.term i).S.base.metric 0).inner (B i y)
            (mfderiv I3 I3 (B i) y v) (mfderiv I3 I3 (B i) y v) ≤
              (1 + eta) * (H i).inner y v v) →
      ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ P : PointedRiemannianManifold.{0, 0, 0} I3,
      ∃ hpath : PathConnectedSpace P.M,
      ∃ tau : ℝ, ∃ htau : 0 < tau,
      ∃ S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)),
      ∃ C : ℕ → PartialDiffeomorph I3 I3 P.M N ∞,
        IsSolutionOn S ∧ S.base.metric 0 = P.metric ∧
        (∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ) ∧
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ i, C i P.basepoint = x (f i)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf P.metric P.basepoint r) ∧
          (∀ᶠ i in atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C i).source ∧
            riemannianClosedBallOf (H (f i)) (x (f i)) (r / 4) ⊆
              (C i) '' riemannianClosedBallOf P.metric P.basepoint r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ i in atTop,
            ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
              ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
                |metricDistance (H (f i)) (C i a) (C i b) - metricDistance P.metric a b| < eta := by
  obtain ⟨epsStar, tau, r0, hepsStar, htau, _, hlimit⟩ :=
    exists_nonnegative_local_backward_limit.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X N top chart smooth t2 H x B R hR hB hBbase hcapture hBconv
  obtain ⟨f, hf, L, V, hp, F, ht0, S, _, hsource, hbase, _, _, _, hpull,
    hconv, _, rho, _, g, hg0, hgsol, hgsec, hgscalar, _⟩ :=
    hlimit eps heps hle sigma hsigma Phi hPhi X
  let P0 : PointedRiemannianManifold.{0, 0, 0} I3 := {
    M := V
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    t2 := inferInstance
    sigmaCompact := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
    t2TangentBundle := inferInstance
    metric := L.metric.restrictOpen V
    basepoint := ⟨L.basepoint, hp⟩ }
  let T : SolutionOn (I := I3) (M := P0.M)
      (RealTimeInterval.closed (-(tau / 2)) 0 (by linarith)) := {base.metric := g}
  have hT : T.base.metric 0 = P0.metric := hg0
  have hscalar0 : metricScalarAt P0.metric P0.basepoint = 1 := by
    rw [← hT]
    exact hgscalar
  have hgsolT : IsSolutionOn T := by
    apply isSolutionOn_cast hgsol
    · change Icc (-tau / 2) 0 = Icc (-(tau / 2)) 0
      congr 1
      ring
    · change Ioo (-tau / 2) 0 = Ioo (-(tau / 2)) 0
      congr 1
      ring
  obtain ⟨U, hpU, hpath, hsolU, hsecU, hscalarU, hmetricU⟩ :=
    exists_connected_terminal_patch P0 T hgsolT hT
      (tau := tau / 2) (by simpa only [T, P0, neg_div] using hgsec) hscalar0
  let _ : PathConnectedSpace U := hpath
  let _ : LocallyCompactSpace P0.M := ChartedSpace.locallyCompactSpace ThreeSpace P0.M
  let _ : SigmaCompactSpace P0.M := P0.sigmaCompact
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let _ : PseudoMetricSpace U := (P0.metric.restrictOpen U).toPseudoMetricSpace
  let _ : MetricSpace U := MetricSpace.ofT0PseudoMetricSpace U
  let P : PointedRiemannianManifold.{0, 0, 0} I3 := {
    M := U
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    t2 := inferInstance
    sigmaCompact := inferInstance
    t2TangentBundle := inferInstance
    metric := P0.metric.restrictOpen U
    basepoint := ⟨P0.basepoint, hpU⟩ }
  have hTU : (solutionOnRestrictOpen T U).base.metric 0 = P.metric := by
    change (T.base.metric 0).restrictOpen U = P0.metric.restrictOpen U
    rw [hT]
  have hmetricP : ∀ a b : P.M, edist a b = riemannianEDistOf P.metric a b := by
    intro a b
    rw [← hTU]
    exact hmetricU a b
  let incV := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) V ⟨L.basepoint, hp⟩
  let incU := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨P0.basepoint, hpU⟩
  let A := fun i => incU.trans (incV.trans (F i))
  have hA (i : ℕ) (y : P.M) : y ∈ (A i).source :=
    ⟨mem_univ _, mem_univ _, hsource i (subset_closure y.val.property)⟩
  have hAbase (i : ℕ) : A i P.basepoint = (X.term (f i)).basepoint := hbase i
  have hAd (i : ℕ) (y : P.M) (v : TangentSpace I3 y) :
      mfderiv I3 I3 (A i) y v = mfderiv I3 I3 (F i) (y.val : L.M) v := by
    have hF := (F i).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      (hsource i (subset_closure y.val.property))
    have hV := (contMDiff_subtype_val (I := I3) (U := V) (n := ∞)).mdifferentiableAt (by simp) (x := y.val)
    have hU := (contMDiff_subtype_val (I := I3) (U := U) (n := ∞)).mdifferentiableAt (by simp) (x := y)
    change mfderiv I3 I3 (((F i : L.M → (X.term (f i)).M) ∘ Subtype.val) ∘ Subtype.val) y v = _
    erw [mfderiv_comp y (hF.comp _ hV) hU, ContinuousLinearMap.comp_apply,
      mfderiv_subtype_val_apply, mfderiv_comp y.val hF hV, ContinuousLinearMap.comp_apply,
      mfderiv_subtype_val_apply]
  let G := fun i => ((S i).base.metric 0).restrictOpen U
  have hG : ∀ i, ∀ y ∈ (A i).source, ∀ v w : TangentSpace I3 y,
      (G i).inner y v w = ((X.term (f i)).S.base.metric 0).inner (A i y)
        (mfderiv I3 I3 (A i) y v) (mfderiv I3 I3 (A i) y w) := by
    intro i y _ v w
    rw [hAd, hAd]
    exact hpull i 0 y.val v w
  have hGconv : MetricCInfConvergenceOnCompacts G P.metric P.metric := hconv.restrictOpen U
  let C := fun i => (A i).trans (B (f i)).symm
  obtain ⟨r, hr, hKr, hCbase, hcover, hdist⟩ :=
    exists_inverse_composition_distance_comparison P.metric hmetricP P.basepoint
      ((X.reindex f hf).toFlowSequence.atTime 0) A
      (fun _ _ => Eventually.of_forall fun i _ _ => hA i _)
      hAbase G hG (fun K hK => hGconv K hK 0)
      (fun i => H (f i)) (fun i => x (f i)) (fun i => B (f i))
      hR (fun i => hB (f i)) (fun i => hBbase (f i)) (fun i => hcapture (f i))
      (fun eta heta => hf.tendsto_atTop (hBconv eta heta))
  refine ⟨f, hf, P, hpath, tau / 2, by positivity, solutionOnRestrictOpen T U, C,
    hsolU, hTU, hsecU, ?_, hCbase, r, hr, hKr, hcover, ?_⟩
  · rw [← hTU]
    exact hscalarU
  · exact hdist


theorem exists_terminal_rescaled_local_backward_limit {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      ∀ f : ℕ → ℕ, StrictMono f →
      ∀ L : PointedRiemannianManifold.{u, 0, 0} I3,
      ∀ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
      ∀ conv : MetricConvergenceData maps,
      (∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
      ∀ W : TopologicalSpace.Opens L.M, ∀ x : ℕ → W,
      ∀ R : ℝ, 0 < R →
      (∀ n, 2 ≤ metricScalarAt L.metric (x n : L.M)) →
      (∀ n, IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
        (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))))) →
      ∃ j k : ℕ → ℕ, StrictMono j ∧ StrictMono k ∧
      ∃ hq : ∀ n, 1 ≤ (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M)),
      let q := fun n => (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M))
      let H := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n))
        (L.metric.restrictOpen W)
      Tendsto (fun n => q n / metricScalarAt L.metric (x (j n) : L.M)) atTop (𝓝 1) ∧
      ∃ P : PointedRiemannianManifold.{0, 0, 0} I3,
      ∃ hpath : PathConnectedSpace P.M,
      ∃ tau : ℝ, ∃ htau : 0 < tau,
      ∃ S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)),
      ∃ C : ℕ → PartialDiffeomorph I3 I3 P.M W ∞,
        IsSolutionOn S ∧ S.base.metric 0 = P.metric ∧
        (∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ) ∧
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, C n P.basepoint = x (j n)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf P.metric P.basepoint r) ∧
          (∀ᶠ n in atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
            riemannianClosedBallOf (H n) (x (j n)) (r / 4) ⊆
              (C n) '' riemannianClosedBallOf P.metric P.basepoint r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
              ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
                |metricDistance (H n) (C n a) (C n b) - metricDistance P.metric a b| < eta := by
  obtain ⟨epsStar, hepsStar, hflow⟩ := exists_local_backward_limit_with_end_comparison.{u, u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf L maps conv hcanonical W x R hR hQ hcompact
  obtain ⟨k, hk, hq, hratio, hcmp⟩ := exists_terminal_rescaled_source_comparison X f hf L
    maps conv hcanonical W x hR hQ hcompact
  let q := fun n => (X.term (f (k n))).S.scalar 0 (maps.partialDiffeomorph (k n) (x n : L.M))
  let H := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n)) (L.metric.restrictOpen W)
  let Y := (X.reindex (f ∘ k) (hf.comp hk)).terminalCurvatureRescale
    (fun n => maps.partialDiffeomorph (k n) (x n : L.M)) hq
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) W ⟨x 0⟩
  let B := fun n => inc.trans (maps.partialDiffeomorph (k n))
  have hBbase (n : ℕ) : B n (x n) = (Y.term n).basepoint := rfl
  have hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (H n) (x n) R, ∀ v : TangentSpace I3 y,
        (1 - eta) * (H n).inner y v v ≤ ((Y.term n).S.base.metric 0).inner (B n y)
          (mfderiv I3 I3 (B n) y v) (mfderiv I3 I3 (B n) y v) ∧
        ((Y.term n).S.base.metric 0).inner (B n y)
          (mfderiv I3 I3 (B n) y v) (mfderiv I3 I3 (B n) y v) ≤
            (1 + eta) * (H n).inner y v v := by
    intro eta heta
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    filter_upwards [hlim.eventually (eventually_lt_nhds heta)] with n hn
    intro y hy v
    have hh := (hcmp n).2.2.1 y hy v
    have hg := metric_inner_self_nonneg (H n) y v
    exact ⟨(mul_le_mul_of_nonneg_right (by linarith : 1 - eta ≤ 1 - 1 / ((n : ℝ) + 2)) hg).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right (by linarith : 1 + 1 / ((n : ℝ) + 2) ≤ 1 + eta) hg)⟩
  obtain ⟨j, hj, P, hpath, tau, htau, S, C, hS, hterminal, hsec, hscalar, hbase, r, hr,
    hK, hcapture, hdist⟩ := hflow eps heps hle sigma hsigma Phi hPhi Y W H x B R hR
      (fun n => (hcmp n).2.1) hBbase (fun n => by
        rw [← hBbase]
        exact (hcmp n).2.2.2.1) hBconv
  refine ⟨j, k ∘ j, hj, hk.comp hj, fun n => hq (j n), ?_⟩
  dsimp only
  refine ⟨hratio.comp hj.tendsto_atTop, P, hpath, tau, htau, S, C, hS, hterminal,
    hsec, hscalar, hbase, r, hr, hK, hcapture, hdist⟩

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

theorem exists_local_backward_limit_on_normalized_end {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      ∀ f : ℕ → ℕ, StrictMono f →
      ∀ L : PointedRiemannianManifold.{u, 0, 0} I3,
      ∀ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
      ∀ conv : MetricConvergenceData maps,
      (∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
      (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
        ∀ y ∈ maps.source i, ∀ v : TangentSpace I3 y,
          (1 - eta) * L.metric.inner y v v ≤
            ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ∧
          ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ≤
            (1 + eta) * L.metric.inner y v v) →
      ∀ W : TopologicalSpace.Opens L.M, ∀ hW : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hW
      let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
      let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
      ∀ q0 : UniformSpace.Completion W, ∀ d : ℝ, 0 < d →
        IsCompact (Metric.closedBall q0 d) →
        Metric.closedBall q0 d ⊆ insert q0 (range (fun x : W => (x : UniformSpace.Completion W))) →
      ∀ x : ℕ → W, Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 q0) →
        Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) atTop atTop →
        (∀ᶠ n in atTop, 196 < metricScalarAt L.metric (x n : L.M) *
          dist (x n : UniformSpace.Completion W) q0 ^ 2) →
      ∃ j k : ℕ → ℕ, StrictMono j ∧ StrictMono k ∧
      ∃ hq : ∀ n, 1 ≤ (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M)),
      let q := fun n => (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M))
      let H := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n))
        (L.metric.restrictOpen W)
      Tendsto (fun n => q n / metricScalarAt L.metric (x (j n) : L.M)) atTop (𝓝 1) ∧
      ∃ P : PointedRiemannianManifold.{0, 0, 0} I3,
      ∃ hpath : PathConnectedSpace P.M,
      ∃ tau : ℝ, ∃ htau : 0 < tau,
      ∃ S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)),
      ∃ C : ℕ → PartialDiffeomorph I3 I3 P.M W ∞,
        IsSolutionOn S ∧ S.base.metric 0 = P.metric ∧
        (∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ) ∧
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, C n P.basepoint = x (j n)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf P.metric P.basepoint r) ∧
          (∀ᶠ n in atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
            riemannianClosedBallOf (H n) (x (j n)) (r / 4) ⊆
              (C n) '' riemannianClosedBallOf P.metric P.basepoint r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
              ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
                |metricDistance (H n) (C n a) (C n b) - metricDistance P.metric a b| < eta := by
  obtain ⟨epsFlow, hepsFlow, hflow⟩ := exists_terminal_rescaled_local_backward_limit.{u} hkappa
  obtain ⟨epsEnd, a, tau0, C0, hepsEnd, ha, _, _, _, hend⟩ :=
    exists_parabolic_curvature_bound_on_normalized_end.{u} hkappa
  refine ⟨min epsFlow epsEnd, lt_min hepsFlow hepsEnd, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf L maps conv hcanonical hcomp W hW
  let _ : PathConnectedSpace W := hW
  dsimp only
  let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
  let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
  intro q0 d hd hKd hcover x hx hQ hquant
  have hbuffer := hend eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi X f hf
    L maps conv hcanonical hcomp W hW hd hKd hcover x hx hQ hquant
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hbuffer.and (hQ.eventually_ge_atTop 2))
  let x' := fun n : ℕ => x (n + N0)
  have hQ' (n : ℕ) : 2 ≤ metricScalarAt L.metric (x' n : L.M) :=
    (hN0 (n + N0) (by omega)).2
  have hK' (n : ℕ) : IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x' n)
      (4 * (2 * a) / Real.sqrt (metricScalarAt L.metric (x' n : L.M)))) := by
    simpa only [x', show (4 : ℝ) * (2 * a) = 8 * a by ring] using
      (hN0 (n + N0) (by omega)).1.2.1
  obtain ⟨j, k, hj, hk, hq, hratio, P, hpath, tau, htau, S, C, hS, hterminal, hsec,
    hscalar, hbase, r, hr, hK, hcapture, hdist⟩ :=
    hflow eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X f hf L maps conv
      hcanonical W x' (2 * a) (by positivity) hQ' hK'
  refine ⟨fun n => j n + N0, k,
    (show StrictMono (fun n : ℕ => n + N0) from fun _ _ h => Nat.add_lt_add_right h N0).comp hj,
    hk, hq, ?_⟩
  dsimp only
  exact ⟨hratio, P, hpath, tau, htau, S, C, hS, hterminal, hsec, hscalar,
    hbase, r, hr, hK, hcapture, hdist⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
