import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Compact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedCurvatureWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedNoncollapse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity

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

def NormalizedSequence.terminalCurvatureRescaledSequence
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)) : PointedRiemannianSeq I3 where
  obj i := { (X.term (f i)).atTime 0 with
    basepoint := x i
    metric := scaleMetric ((X.term (f i)).S.scalar 0 (x i)) (hQ i)
      ((X.term (f i)).S.base.metric 0) }

private theorem rescaled_sequence_complete
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)) :
    SeqMetricComplete (X.terminalCurvatureRescaledSequence f x hQ) := by
  constructor
  intro i
  have hzero : (0 : ℝ) ∈ (X.interval (f i)).carrier := by
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (f i)], le_rfl⟩
  have hcomplete : RiemannianMetricComplete ((X.term (f i)).S.base.metric 0) :=
    ⟨X.complete (f i) 0 hzero⟩
  have hscaled : RiemannianMetricComplete (scaleMetric ((X.term (f i)).S.scalar 0 (x i))
      (hQ i) ((X.term (f i)).S.base.metric 0)) :=
    hcomplete.of_lower (hQ i) (fun y v => by simp only [scaleMetric_inner, le_refl])
  exact hscaled.complete

private theorem rescaled_sequence_ball_subset
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hQr : Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i) * r i ^ 2) atTop atTop)
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ i in atTop, ∀ y : (X.term (f i)).M,
      riemannianEDistOf ((X.terminalCurvatureRescaledSequence f x hQ).obj i).metric
        (x i) y ≤ ENNReal.ofReal R →
      metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i := by
  filter_upwards [hQr.eventually_ge_atTop (R ^ 2)] with i hi y hy
  have hd : Real.sqrt ((X.term (f i)).S.scalar 0 (x i)) *
      metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ R := by
    have h := ENNReal.toReal_le_of_le_ofReal hR hy
    change (riemannianEDistOf (scaleMetric ((X.term (f i)).S.scalar 0 (x i)) (hQ i)
      ((X.term (f i)).S.base.metric 0)) (x i) y).toReal ≤ R at h
    rw [edistOf_scale, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
    exact h
  have hs : 0 < Real.sqrt ((X.term (f i)).S.scalar 0 (x i)) := Real.sqrt_pos.mpr (hQ i)
  have hsq := Real.sq_sqrt (hQ i).le
  have hlarge : R ≤ Real.sqrt ((X.term (f i)).S.scalar 0 (x i)) * r i := by
    apply (sq_le_sq₀ hR (mul_nonneg hs.le (hr i).le)).mp
    rwa [mul_pow, hsq]
  exact (mul_le_mul_iff_right₀ hs).mp (hd.trans hlarge)

private theorem rescaled_sequence_local_jets
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (hf : StrictMono f) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlarge : Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop)
    (hQr : Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i) * r i ^ 2) atTop atTop)
    (hbound : ∀ i y, metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
      (X.term (f i)).S.scalar 0 y ≤ 2 * (X.term (f i)).S.scalar 0 (x i))
    (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (hjets : ∀ᶠ i in atTop, ∀ Q : ℝ, 1 ≤ Q → ∀ p : (X.term i).M,
      (X.term i).S.scalar 0 p ≤ Q → ∀ m : ℕ,
        curvDerivNorm m ((X.term i).S.base.metric 0) p ≤ B m * Q * Real.sqrt Q ^ m) :
    ∀ R : ℝ, 0 < R → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
      HasLocalCurvDerivBound ((X.terminalCurvatureRescaledSequence f x hQ).obj i)
        (x i) R m C := by
  intro R hR m
  refine ⟨2 * B m * Real.sqrt 2 ^ m, mul_nonneg (mul_nonneg (by norm_num) (hB m))
    (by positivity), ?_⟩
  filter_upwards [rescaled_sequence_ball_subset X f x hQ r hr hQr hR.le,
    hf.tendsto_atTop.eventually hjets, hlarge.eventually_ge_atTop 1] with i hi hji hQi
  intro y hy
  change (X.term (f i)).M at y
  have hscal := hbound i y (hi y hy)
  let Q := (X.term (f i)).S.scalar 0 (x i)
  have hj := hji (2 * Q) (by dsimp only [Q]; linarith) y hscal m
  change curvDerivNorm m (scaleMetric Q (hQ i) ((X.term (f i)).S.base.metric 0)) y ≤ _
  rw [curvDerivNorm_scaleMetric]
  apply (div_le_iff₀ (mul_pos (hQ i) (pow_pos (Real.sqrt_pos.mpr (hQ i)) m))).mpr
  calc
    _ ≤ B m * (2 * Q) * Real.sqrt (2 * Q) ^ m := hj
    _ = (2 * B m * Real.sqrt 2 ^ m) * (Q * Real.sqrt Q ^ m) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
      ring

private theorem rescaled_sequence_noncollapsed
    {eps kappa sigma kappa' : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hnc : X.TerminalSliceNoncollapsed kappa') (f : ℕ → ℕ) (hf : StrictMono f)
    (x : ∀ i, (X.term (f i)).M) (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)) :
    ∀ᶠ i in atTop, MetricNoncollapsed ((X.terminalCurvatureRescaledSequence f x hQ).obj i)
      kappa' (Ioc 0 (Real.sqrt ((X.term (f i)).S.scalar 0 (x i)))) := by
  filter_upwards [hf.tendsto_atTop.eventually hnc.eventually_metricNoncollapsed_scaleMetric]
    with i hi
  exact hi _ (hQ i) (x i)


private theorem rescaled_sequence_local_injectivity
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {kappa' : ℝ} (hnc : X.TerminalSliceNoncollapsed kappa')
    (f : ℕ → ℕ) (hf : StrictMono f) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i))
    (hlarge : Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop)
    (hjets : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
      HasLocalCurvDerivBound ((X.terminalCurvatureRescaledSequence f x hQ).obj i)
        (x i) R 0 C) :
    ∀ R : ℝ, 0 < R → ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf ((X.terminalCurvatureRescaledSequence f x hQ).obj i).metric
        (x i) R, HasInjRadiusAt ((X.terminalCurvatureRescaledSequence f x hQ).obj i) y rho := by
  intro R hR
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hnc.1
  obtain ⟨C, hC, hbound⟩ := hjets (R + 1) (by linarith)
  let r : ℝ := (C ^ 2 + 1)⁻¹
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := (inv_le_one₀ (by positivity : 0 < C ^ 2 + 1)).mpr (by nlinarith)
  have hrc : r * C ^ 2 ≤ 1 := by
    calc
      _ ≤ r * (C ^ 2 + 1) := by nlinarith
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hscaled : r ^ 4 * C ^ 2 ≤ 1 := by
    calc
      _ = r ^ 3 * (r * C ^ 2) := by ring
      _ ≤ 1 ^ 3 * 1 := mul_le_mul (pow_le_pow_left₀ hr.le hr1 3) hrc
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  refine ⟨iota * r, mul_pos hiota hr, ?_⟩
  filter_upwards [hbound, rescaled_sequence_noncollapsed X hnc f hf x hQ,
    hlarge.eventually_ge_atTop 1] with i hi hsi hQi
  intro y hy
  let Y := (X.terminalCurvatureRescaledSequence f x hQ).obj i
  have hcurv : ∀ z ∈ riemannianBallOf Y.metric y r,
      r ^ 4 * Tensor0SBundle.normSq0S Y.metric z 4 (metricRm04At Y.metric z) ≤ 1 := by
    intro z hz
    have hz' : z ∈ riemannianClosedBallOf Y.metric (x i) (R + 1) := by
      calc
        _ ≤ riemannianEDistOf Y.metric (x i) y + riemannianEDistOf Y.metric y z :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal R + ENNReal.ofReal 1 :=
          add_le_add hy (hz.le.trans (ENNReal.ofReal_le_ofReal hr1))
        _ = ENNReal.ofReal (R + 1) := (ENNReal.ofReal_add hR.le zero_le_one).symm
    have hj := hi z hz'
    have hsq : Tensor0SBundle.normSq0S Y.metric z 4 (metricRm04At Y.metric z) ≤ C ^ 2 := by
      apply le_sq_of_sqrt_le (Tensor0SBundle.normSq0S_nonneg _ _ _ _)
      change Real.sqrt (Tensor0SBundle.normSq0S Y.metric z 4 (metricRm04 Y.metric z)) ≤ C at hj
      rwa [metricRm04_apply] at hj
    exact (mul_le_mul_of_nonneg_left hsq (pow_nonneg hr.le 4)).trans hscaled
  have hrscale : r ≤ Real.sqrt ((X.term (f i)).S.scalar 0 (x i)) := by
    have hq : 1 ≤ Real.sqrt ((X.term (f i)).S.scalar 0 (x i)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQi
    exact hr1.trans hq
  have hvol := hsi y r ⟨hr, hrscale⟩ hr hcurv
  have hvol' : ENNReal.ofReal (kappa' * r ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure I3 Y.M Y.metric (riemannianBallOf Y.metric y r) := by
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] using hvol
  have hcomplete : RiemannianMetricComplete Y.metric :=
    ⟨(rescaled_sequence_complete X f x hQ).complete i⟩
  exact hasInjRadiusAt_of_expMap_injOn Y y (mul_pos hiota hr)
    (hinj Y.M Y.metric hcomplete y r hr hcurv hvol')

private theorem rescaled_sequence_pinching
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)) :
    ∀ i (y : ((X.terminalCurvatureRescaledSequence f x hQ).obj i).M),
      curvatureOperatorLowerBoundAt ((X.terminalCurvatureRescaledSequence f x hQ).obj i).metric y
        (metricAlgebraicCurvatureTensorAt ((X.terminalCurvatureRescaledSequence f x hQ).obj i).metric y)
        (rescalePinchingFunction ((X.term (f i)).S.scalar 0 (x i) * X.scale (f i)) Phi
          (metricScalarAt ((X.terminalCurvatureRescaledSequence f x hQ).obj i).metric y)) := by
  intro i y
  change (X.term (f i)).M at y
  have hzero : (0 : ℝ) ∈ (X.interval (f i)).carrier := by
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (f i)], le_rfl⟩
  let Q := (X.term (f i)).S.scalar 0 (x i)
  let g := (X.term (f i)).S.base.metric 0
  change curvatureOperatorLowerBoundAt (scaleMetric Q (hQ i) g) y
    (metricAlgebraicCurvatureTensorAt (scaleMetric Q (hQ i) g) y)
    (rescalePinchingFunction (Q * X.scale (f i)) Phi
      (metricScalarAt (scaleMetric Q (hQ i) g) y))
  rw [metricAlgebraicCurvatureTensorAt_scaleMetric, curvatureOperatorLowerBoundAt_scaleMetric,
    metricScalarAt_scaleMetric]
  have heq : Q * rescalePinchingFunction (Q * X.scale (f i)) Phi
      (Q⁻¹ * metricScalarAt g y) = rescalePinchingFunction (X.scale (f i)) Phi
      (metricScalarAt g y) := by
    simp only [rescalePinchingFunction, mul_inv]
    have harg : Q * X.scale (f i) * (Q⁻¹ * metricScalarAt g y) =
        X.scale (f i) * metricScalarAt g y := by
      calc
        _ = (Q * Q⁻¹) * (X.scale (f i) * metricScalarAt g y) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (hQ i).ne', one_mul]
    rw [harg, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (hQ i).ne', one_mul]
  rw [heq]
  exact X.pinching (f i) 0 hzero y


theorem exists_terminalCurvatureRescaledSequence_metric_limit_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ BoundedAtDistance X →
          ∃ D : ℝ, 0 < D ∧ ∃ f : ℕ → ℕ, StrictMono f ∧
            ∃ (x : ∀ i, (X.term (f i)).M) (r : ℕ → ℝ)
              (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)),
              (∀ i, 1 ≤ (X.term (f i)).S.scalar 0 (x i)) ∧
              (∀ i, 0 < r i) ∧
              Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop ∧
              Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
              (∀ i y, metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
                metricDistance ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint y < D ∧
                (X.term (f i)).S.scalar 0 y ≤ 2 * (X.term (f i)).S.scalar 0 (x i)) ∧
              ∃ P : MetricCompactLimit (X.terminalCurvatureRescaledSequence f x hQ),
                (∀ k, P.convergence.metrics.domain k =
                  CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
                ConnectedSpace P.limit.M ∧
                (∀ n, IsCompact (closure (P.maps.source n))) ∧
                (∀ n, IsConnected (P.maps.source n)) ∧
                (∀ n, closure (P.maps.source n) ⊆ P.maps.source (n + 1)) ∧
                metricScalarAt P.limit.metric P.limit.basepoint = 1 ∧
                (∀ y : P.limit.M, metricScalarAt P.limit.metric y ≤ 2) ∧
                (∀ (y : P.limit.M) (v w : TangentSpace I3 y),
                  0 ≤ metricRm04StandardAt P.limit.metric y v w w v) ∧
                ∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' univ := by
  obtain ⟨epsJet, hepsJet, B, hB, hjet⟩ :=
    exists_curvDerivNorm_bound_at_terminal_scalar_scale.{u} hkappa
  obtain ⟨epsNC, hepsNC, hncAll⟩ := exists_terminalSliceNoncollapsed.{u} hkappa
  refine ⟨min epsJet epsNC, lt_min hepsJet hepsNC, ?_⟩
  intro eps heps hle' sigma hsigma Phi hPhi X hfail
  have hle : eps ≤ epsJet := hle'.trans (min_le_left _ _)
  obtain ⟨kappa', hkappa', hncX⟩ := hncAll Phi hPhi
  have hnc := hncX eps heps (hle'.trans (min_le_right _ _)) sigma X
  obtain ⟨D, hD, f₀, hf₀, x₀, r₀, hr₀, hlarge₀, hQr₀, hcontrol₀⟩ :=
    X.exists_terminal_scalar_point_selection hfail
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlarge₀.eventually_ge_atTop 1)
  let shift : ℕ → ℕ := fun i => i + N
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_right h N
  let f := f₀ ∘ shift
  have hf : StrictMono f := hf₀.comp hshift
  let x := fun i => x₀ (shift i)
  let r := r₀ ∘ shift
  have hr := fun i => hr₀ (shift i)
  have hlarge := hlarge₀.comp hshift.tendsto_atTop
  have hQr := hQr₀.comp hshift.tendsto_atTop
  have hcontrol := fun i => hcontrol₀ (shift i)
  have hQone : ∀ i, 1 ≤ (X.term (f i)).S.scalar 0 (x i) := fun i =>
    hN (shift i) (Nat.le_add_left N i)
  let hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i) := fun i => (hr i).2.2.2
  let Y := X.terminalCurvatureRescaledSequence f x hQ
  have hjets := rescaled_sequence_local_jets X f hf x hQ r (fun i => (hr i).1)
    hlarge hQr (fun i y hy => (hcontrol i y hy).2) B hB
    (hjet eps heps hle sigma hsigma Phi hPhi X)
  obtain ⟨P, hcanonical, href, hconnected, hcompact, hsourceconn, hnested⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      Y (rescaled_sequence_complete X f x hQ) (fun i => X.connected (f i)) hjets
      (rescaled_sequence_local_injectivity X hnc f hf x hQ hlarge
        (fun R hR => hjets R hR 0))
  refine ⟨D + 1, by linarith, f, hf, x, r, hQ, hQone, (fun i => (hr i).1),
    hlarge, hQr, hcontrol, P, hcanonical, hconnected, hcompact, hsourceconn, hnested, ?_, ?_, ?_, ?_⟩
  · apply KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains
      P.convergence.metrics hcanonical
    intro i
    change metricScalarAt (scaleMetric ((X.term (f (P.subseq i))).S.scalar 0 (x (P.subseq i)))
      (hQ (P.subseq i)) ((X.term (f (P.subseq i))).S.base.metric 0)) (x (P.subseq i)) = 1
    rw [metricScalarAt_scaleMetric]
    exact inv_mul_cancel₀ (hQ (P.subseq i)).ne'
  · intro y
    let : ConnectedSpace P.limit.M := hconnected
    obtain ⟨R, hR, hmaps⟩ := P.maps.exists_eventually_image_compact_subset_ball
      P.convergence.metrics href P.limit_complete (K := {y}) isCompact_singleton
    have hball := rescaled_sequence_ball_subset X f x hQ r (fun i => (hr i).1) hQr hR.le
    apply le_of_tendsto (KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains
      P.convergence.metrics hcanonical y)
    filter_upwards [hmaps, P.strictMono.tendsto_atTop.eventually hball] with i hi hbi
    have hy := hi.2 (mem_image_of_mem (P.maps.map i) (mem_singleton y))
    let z : (X.term (f (P.subseq i))).M := P.maps.map i y
    have hscal := (hcontrol (P.subseq i) z (hbi z hy)).2
    change metricScalarAt (scaleMetric ((X.term (f (P.subseq i))).S.scalar 0 (x (P.subseq i)))
      (hQ (P.subseq i)) ((X.term (f (P.subseq i))).S.base.metric 0)) z ≤ 2
    rw [metricScalarAt_scaleMetric]
    calc
      _ ≤ ((X.term (f (P.subseq i))).S.scalar 0 (x (P.subseq i)))⁻¹ *
          (2 * (X.term (f (P.subseq i))).S.scalar 0 (x (P.subseq i))) :=
        mul_le_mul_of_nonneg_left hscal (inv_nonneg.mpr (hQ (P.subseq i)).le)
      _ = 2 * (((X.term (f (P.subseq i))).S.scalar 0 (x (P.subseq i)))⁻¹ *
          (X.term (f (P.subseq i))).S.scalar 0 (x (P.subseq i))) := by ring
      _ = 2 := by rw [inv_mul_cancel₀ (hQ (P.subseq i)).ne', mul_one]
  · apply sectional_nonnegative_of_pointed_admissible_pinching
      P.convergence.metrics hcanonical hPhi
      (fun i => (X.term (f i)).S.scalar 0 (x i) * X.scale (f i))
      (fun i => mul_pos (hQ i) (X.scale_pos (f i)))
      ((hlarge.atTop_mul_atTop₀ (X.scale_tendsto.comp hf.tendsto_atTop)).comp
        P.strictMono.tendsto_atTop)
    exact rescaled_sequence_pinching X f x hQ
  · refine ⟨kappa', hkappa', ?_⟩
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    have hsource := P.strictMono.tendsto_atTop.eventually
      (rescaled_sequence_noncollapsed X hnc f hf x hQ)
    have hn := KappaSolutions.tensor_noncollapsed_of_eventually_pointed_canonical_convergence
      P.convergence.metrics hcanonical P.limit_complete kappa' (by
        intro s hs
        filter_upwards [hsource, P.strictMono.tendsto_atTop.eventually
          ((Real.tendsto_sqrt_atTop.comp hlarge).eventually_ge_atTop s)] with i hi hsi y hcurv
        have h := hi y s ⟨hs, hsi⟩ hs hcurv
        simpa only [hdim, ENNReal.ofReal_mul hkappa'.le, ENNReal.ofReal_pow hs.le] using h)
    intro y s _ hs hcurv
    simpa only [hdim, ENNReal.ofReal_mul hkappa'.le, ENNReal.ofReal_pow hs.le] using
      hn y s hs hcurv

private theorem rescaled_sequence_basepoint_escapes
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (hf : StrictMono f) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i))
    (hlarge : Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop)
    {rho C : ℝ} (hrho : 0 < rho)
    (hbound : ∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf ((X.term i).S.base.metric 0)
      (X.term i).basepoint rho, (X.term i).S.scalar 0 y ≤ C) :
    Tendsto (fun i => (riemannianEDistOf
      ((X.terminalCurvatureRescaledSequence f x hQ).obj i).metric
      (x i) (X.term (f i)).basepoint).toReal) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ ((Real.tendsto_sqrt_atTop.comp hlarge).atTop_mul_const hrho)
  filter_upwards [hf.tendsto_atTop.eventually hbound, hlarge.eventually_gt_atTop C]
    with i hi hQi
  have : ConnectedSpace (X.term (f i)).M := X.connected (f i)
  have hdist : rho ≤ (riemannianEDistOf ((X.term (f i)).S.base.metric 0)
      (X.term (f i)).basepoint (x i)).toReal := by
    by_contra hd
    have hmem : x i ∈ riemannianClosedBallOf ((X.term (f i)).S.base.metric 0)
        (X.term (f i)).basepoint rho :=
      (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top _ _ _) hrho.le).mpr
        (le_of_not_ge hd)
    exact (not_le.mpr hQi) (hi (x i) hmem)
  change _ ≤ (riemannianEDistOf (scaleMetric ((X.term (f i)).S.scalar 0 (x i)) (hQ i)
    ((X.term (f i)).S.base.metric 0)) (x i) (X.term (f i)).basepoint).toReal
  rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    riemannianEDistOf_comm ((X.term (f i)).S.base.metric 0)]
  exact mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg _)

theorem exists_terminalCurvatureRescaledSequence_noncompact_metric_limit_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ BoundedAtDistance X →
          ∃ D : ℝ, 0 < D ∧ ∃ f : ℕ → ℕ, StrictMono f ∧
            ∃ (x : ∀ i, (X.term (f i)).M) (r : ℕ → ℝ)
              (hQ : ∀ i, 0 < (X.term (f i)).S.scalar 0 (x i)),
              (∀ i, 1 ≤ (X.term (f i)).S.scalar 0 (x i)) ∧
              (∀ i, 0 < r i) ∧
              Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop ∧
              Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
              (∀ i y, metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
                metricDistance ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint y < D ∧
                (X.term (f i)).S.scalar 0 y ≤ 2 * (X.term (f i)).S.scalar 0 (x i)) ∧
              ∃ P : MetricCompactLimit (X.terminalCurvatureRescaledSequence f x hQ),
                (∀ k, P.convergence.metrics.domain k =
                  CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
                ConnectedSpace P.limit.M ∧ NoncompactSpace P.limit.M ∧
                (∀ n, IsCompact (closure (P.maps.source n))) ∧
                (∀ n, IsConnected (P.maps.source n)) ∧
                (∀ n, closure (P.maps.source n) ⊆ P.maps.source (n + 1)) ∧
                metricScalarAt P.limit.metric P.limit.basepoint = 1 ∧
                (∀ y : P.limit.M, metricScalarAt P.limit.metric y ≤ 2) ∧
                (∀ (y : P.limit.M) (v w : TangentSpace I3 y),
                  0 ≤ metricRm04StandardAt P.limit.metric y v w w v) ∧
                ∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' univ := by
  obtain ⟨e₀, he₀, hlimit⟩ :=
    exists_terminalCurvatureRescaledSequence_metric_limit_of_not_boundedAtDistance.{u} hkappa
  obtain ⟨e₁, c, C, he₁, hc, _, hprop⟩ :=
    exists_parabolic_curvature_bound_at_terminal_scalar_scale.{u} hkappa
  refine ⟨min e₀ e₁, lt_min he₀ he₁, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hfail
  obtain ⟨D, hD, f, hf, x, r, hQ, hQone, hr, hlarge, hQr, hcontrol,
    P, hcanonical, hconnected, hcompact, hsourceconn, hnested, hbase, hupper, hsec, hnc⟩ :=
    hlimit eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X hfail
  have hball : ∀ᶠ i in atTop, ∀ y ∈ riemannianClosedBallOf ((X.term i).S.base.metric 0)
      (X.term i).basepoint c, (X.term i).S.scalar 0 y ≤ 9 * C := by
    filter_upwards [hprop eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi X]
      with i hi y hy
    have hb := (hi 1 le_rfl (X.term i).basepoint (X.base_one i).le).2
      0 ⟨by linarith, le_rfl⟩ y (by simpa only [Real.sqrt_one, div_one] using hy)
    rw [mul_one] at hb
    have hs := scalar_abs_le_rm (I := I3) ((X.term i).S.base.metric 0) y
    have hdim : Module.finrank ℝ (TangentSpace I3 y) = 3 := by
      change Module.finrank ℝ ThreeSpace = 3
      simp [ThreeSpace]
    rw [hdim] at hs
    norm_num at hs
    exact (le_abs_self _).trans (hs.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
  have hescape := rescaled_sequence_basepoint_escapes X f hf x hQ hlarge hc hball
  refine ⟨D, hD, f, hf, x, r, hQ, hQone, hr, hlarge, hQr, hcontrol,
    P, hcanonical, hconnected, ?_, hcompact, hsourceconn, hnested, hbase, hupper, hsec, hnc⟩
  apply P.maps.noncompact_of_escaping_points P.convergence.metrics
    (fun i => by rw [hcanonical i]; rfl) (fun i => X.connected (f (P.subseq i)))
    (fun i => (X.term (f (P.subseq i))).basepoint)
  exact hescape.comp P.strictMono.tendsto_atTop

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
