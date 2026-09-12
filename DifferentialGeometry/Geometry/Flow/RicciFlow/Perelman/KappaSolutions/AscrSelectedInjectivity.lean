import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrThreeLocalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackSelectedInjectivity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance ascrSelectedInjMeasurableE : MeasurableSpace E := borel E
private local instance ascrSelectedInjBorelE : BorelSpace E := ⟨rfl⟩
local instance ascrSelectedInjTopology : TopologicalSpace F.M := F.topology
local instance ascrSelectedInjCharted : ChartedSpace H F.M := F.charted
local instance ascrSelectedInjSmooth : IsManifold I ∞ F.M := F.smooth
local instance ascrSelectedInjC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ascrSelectedInjSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ascrSelectedInjT2 : T2Space F.M := F.t2
local instance ascrSelectedInjTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem ascrSelectedInj_edist_comm
    (g : SmoothRiemannianMetric I F.M) (y z : F.M) :
    riemannianEDistOf (I := I) g y z = riemannianEDistOf (I := I) g z y := by
  let _ : RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I y z = Manifold.riemannianEDist I z y
  exact Manifold.riemannianEDist_comm (I := I) (x := y) (y := z)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def terminalCurvatureNormalizedFlowSeq_three_baseInjBound
    (hF : IsAncientKappaSolution (I := I) kappa F) (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hlarge : ∀ i, 1 / 4 < r i * Real.sqrt (F.S.scalar 0 (x i))) :
    FlowScaleInjectivityBound (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ) := by
  classical
  let hscale := exists_uniform_local_jacobi_scale
    (Module.finrank ℝ E) (R := (1 / 4 : ℝ)) (K := 7) (by norm_num) (by norm_num)
  let rJ : ℝ := hscale.choose
  have hrJ : 0 < rJ := hscale.choose_spec.1
  have hrJQuarter : rJ ≤ 1 / 4 := hscale.choose_spec.2.1
  have herror := hscale.choose_spec.2.2
  let R : ℝ := min rJ (Real.pi / Real.sqrt 7)
  have hR : 0 < R := lt_min hrJ (div_pos Real.pi_pos (by positivity))
  have hRj : R ≤ rJ := min_le_left _ _
  have hRQuarter : R ≤ 1 / 4 := hRj.trans hrJQuarter
  have hRpi : R ≤ Real.pi / Real.sqrt 7 := min_le_right _ _
  have hs : 0 < R / 8 := by positivity
  have hsQuarter : R / 8 ≤ 1 / 4 := by linarith
  have hη : 0 < selectedCGTInjRadius E kappa R :=
    selectedCGTInjRadius_pos (E := E) hK.kappa_pos hR
  let Y := (terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)
  refine { ρ := selectedCGTInjRadius E kappa R, pos := hη, bound := ?_ }
  intro i
  refine ⟨hη, ?_⟩
  intro hcomplete
  let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
  let _ : ChartedSpace H (Y.obj i).M := (Y.obj i).charted
  let _ : IsManifold I ∞ (Y.obj i).M := (Y.obj i).smooth
  let _ : IsManifold I 1 (Y.obj i).M :=
    IsManifold.of_le (I := I) (M := (Y.obj i).M) (n := ∞) (by decide)
  let _ : T2Space (Y.obj i).M := (Y.obj i).t2
  let _ : SigmaCompactSpace (Y.obj i).M := (Y.obj i).sigmaCompact
  let _ : T2Space (TangentBundle I (Y.obj i).M) := (Y.obj i).t2TangentBundle
  let _ : RiemannianBundle (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle (I := I)
  let _ : (y : (Y.obj i).M) → InnerProductSpace ℝ (TangentSpace I y) :=
    (Y.obj i).riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E (fun y : (Y.obj i).M => TangentSpace I y) :=
    (Y.obj i).riemBundle_cont (I := I)
  let _ : EMetricSpace (Y.obj i).M := (Y.obj i).emetricSpace (I := I)
  have : IsRiemannianManifold I (Y.obj i).M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace (Y.obj i).M := MetricComplete.complete (I := I) (Y.obj i) hcomplete
  let _ : ConnectedSpace (Y.obj i).M := hK.connected
  let hEnorm : IsMetricNorm (I := I) (Y.obj i).metric := by
    intro y v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) (Y.obj i).metric y v
  let g : @SmoothRiemannianMetric E _ _ H _ I F.M F.topology F.charted F.smooth :=
    scaleMetric (F.S.scalar 0 (x i)) (hQ i)
      (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
  have hmetric : g = scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0) := by
    dsimp only [g]
    rw [parabolicTime_zero]
  have hRm : ∀ y : (Y.obj i).M,
      riemannianEDist I (Y.obj i).basepoint y < ENNReal.ofReal (1 / 4) →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (Y.obj i).metric y 4
        (metricRm04At (I := I) (Y.obj i).metric y)) ≤ 7 := by
    intro y hy
    have hyOf : @riemannianEDistOf E _ _ H _ I (Y.obj i).M
        (Y.obj i).topology (Y.obj i).charted (Y.obj i).smooth
        (Y.obj i).metric (Y.obj i).basepoint y <
        ENNReal.ofReal (1 / 4) := by
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm]
      exact hy
    change F.M at y
    change riemannianEDistOf (I := I) g (x i) y < ENNReal.ofReal (1 / 4) at hyOf
    have hyreal : (riemannianEDistOf (I := I) (M := F.M) g y (x i)).toReal <
        r i * Real.sqrt (F.S.scalar 0 (x i)) := by
      exact (congrArg ENNReal.toReal (ascrSelectedInj_edist_comm F g y (x i))).trans_lt
        ((ENNReal.toReal_lt_of_lt_ofReal hyOf).trans (hlarge i))
    have hsq := terminalCurvatureNormalizedFlowSeq_three_rmNormSq_bound
      F hF hK hdim x hQ i (r i) (hlocal i) (s := 0) le_rfl y hyreal
    change Tensor0SBundle.normSq0S (I := I) (M := F.M) g y 4
      (metricRm04 (I := I) (M := F.M) g y) ≤ 48 at hsq
    rw [metricRm04_apply] at hsq
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
      (metricRm04At (I := I) g y)) ≤ 7
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, hsq.trans (by norm_num)⟩
  have hnonneg := terminalCurvatureNormalizedFlowSeq_nonnegativeCurvatureOperator
    F hK x hQ i (s := 0) le_rfl
  have hRic : RicciBoundedBelow (I := I) (Y.obj i).metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) := by
    intro y v
    change F.M at y
    change TangentSpace I y at v
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) g y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) g y).mpr
      intro m c a b
      have ht := hnonneg y m c a b
      change 0 ≤ ∑ j, ∑ l, c j * c l *
        (metricRm04 (I := I) (M := F.M) g y)
          (vec4 (I := I) (a j) (b j) (b l) (a l)) at ht
      simpa only [metricRm04StandardAt_apply, metricRm04_apply] using ht
    have h := metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (I := I) g y hcone v
    change (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) *
      g.inner y v v ≤ ricciTensor (I := I) g y v v
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, neg_zero, zero_mul,
      metricRicciAt_apply_eq_ricciTensor] using h
  have hdomain : riemannianBallOf (I := I) g (x i) (R / 8) ⊆
      {z : F.M | (riemannianEDistOf (I := I) g z (x i)).toReal <
        r i * Real.sqrt (F.S.scalar 0 (x i))} := by
    intro z hz
    change riemannianEDistOf (I := I) g (x i) z < ENNReal.ofReal (R / 8) at hz
    change (riemannianEDistOf (I := I) g z (x i)).toReal < _
    exact (congrArg ENNReal.toReal (ascrSelectedInj_edist_comm F g z (x i))).trans_lt
      (((ENNReal.toReal_lt_of_lt_ofReal hz).trans_le hsQuarter).trans (hlarge i))
  have hdomainScaled : riemannianBallOf (I := I)
      (scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0)) (x i) (R / 8) ⊆
      {z : F.M | (riemannianEDistOf (I := I)
        (scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0)) z (x i)).toReal <
          r i * Real.sqrt (F.S.scalar 0 (x i))} := by
    simpa only [hmetric] using hdomain
  have hvolScaled := terminalCurvatureNormalizedFlowSeq_three_smallBall_volume
    F hF hK hdim x hQ i (r i) (hlocal i) (x i) (R / 8) hs hsQuarter hdomainScaled
  have hvolOf : ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ 3 ≤
      riemannianVolumeMeasure (I := I) (M := F.M) g
        (riemannianBallOf (I := I) g (x i) (R / 8)) := by
    simpa only [hmetric] using hvolScaled
  have hvol : ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDist I (Y.obj i).basepoint y <
          ENNReal.ofReal (R / 8)} := by
    change ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ 3 ≤
      riemannianVolumeMeasure (I := I) (M := (Y.obj i).M) (Y.obj i).metric
        {y : (Y.obj i).M | riemannianEDistOf (I := I) (Y.obj i).metric
          (Y.obj i).basepoint y < ENNReal.ofReal (R / 8)} at hvolOf
    simpa only [hdim,
      riemannianEDistOf_eq_riemannianEDist (I := I) (Y.obj i).metric hEnorm] using hvolOf
  have hcgt := intrInj_ge_vol_of_ball (I := I) (Y.obj i).metric hEnorm
    (Y.obj i).basepoint (K := 7) (ρ := (1 / 4 : ℝ)) (R := R)
    (by norm_num) hR hRQuarter hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRj))
    (r₀ := R / 8) (s := R / 8) hs hs (by linarith) (by linarith)
    (q := 0) (by norm_num) hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  rw [hhalf, hadd] at hcgt
  have hinj := (selectedCGTInjRadius_le_quotient (E := E) hK.kappa_pos.le hR).trans hcgt
  simpa only [Y, PointedRiemannianManifold.intrinsicInjRadius] using hinj

theorem exists_terminalCurvatureNormalizedFlowSeq_three_baseInjBound_tail
    (hF : IsAncientKappaSolution (I := I) kappa F) (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3)
    (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop) :
    ∃ N : ℕ, Nonempty (FlowScaleInjectivityBound (I := I)
      (terminalCurvatureNormalizedFlowSeq F hK (fun i => x (N + i))
        (fun i => hQ (N + i)))) := by
  have hevent : ∀ᶠ i in atTop, 1 / 4 < r i * Real.sqrt (F.S.scalar 0 (x i)) :=
    hexpand (eventually_gt_atTop (1 / 4))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ⟨terminalCurvatureNormalizedFlowSeq_three_baseInjBound F hF hK hdim
    (fun i => x (N + i)) (fun i => r (N + i)) (fun i => hQ (N + i))
    (fun i => hlocal (N + i)) ?_⟩⟩
  intro i
  exact hN (N + i) (Nat.le_add_right N i)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
