import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianLineLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.IntrinsicLineNullPlane
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance terminalNormalizedLineOne {N : Type*} [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] : IsManifold I 1 N :=
  IsManifold.of_le (I := I) (M := N) (n := ∞) (by decide)

section ExactTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance terminalLineTransportTopology : TopologicalSpace L.M := L.topology
local instance terminalLineTransportCharted : ChartedSpace H L.M := L.charted
local instance terminalLineTransportSmooth : IsManifold I ∞ L.M := L.smooth

private theorem terminalLine_of_exact_sequence [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hX : X = spatialRescaledPointedSeq g x lam hlam)
    (hescape : Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => lam i *
      (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop)
    {psi : ℕ → ℕ} (hpsi : StrictMono psi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L psi)
    (C : MetricConvergenceData (I := I) Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M) :
    ∃ gamma : ℝ → L.M, gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  subst X
  obtain ⟨gamma, -, hbase, hline⟩ :=
    exists_riemannian_line_of_rescaled_pointed_convergence
      g hg hsec p x lam hlam hescape hscaled hpsi Phi C hreference hcomplete hconnected
  exact ⟨gamma, hbase, hline⟩

end ExactTransport

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalLineFlowTopology : TopologicalSpace F.M := F.topology
local instance terminalLineFlowCharted : ChartedSpace H F.M := F.charted
local instance terminalLineFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalLineFlowT2 : T2Space F.M := F.t2
local instance terminalLineFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance terminalLineLimitTopology : TopologicalSpace L.M := L.topology
local instance terminalLineLimitCharted : ChartedSpace H L.M := L.charted
local instance terminalLineLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance terminalLineLimitT2 : T2Space L.M := L.t2
local instance terminalLineLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

theorem exists_line_of_terminalCurvatureNormalizedFlowSeq_limit
    [NeZero (Module.finrank ℝ E)]
    {kappa : ℝ} (hK : KLim kappa F)
    (p : F.M) (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hescape : Tendsto
      (fun i => (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
      (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal) atTop atTop)
    {psi : ℕ → ℕ} (hpsi : StrictMono psi)
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) L psi)
    (C : MetricConvergenceData (I := I) Phi)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M) :
    ∃ gamma : ℝ → L.M, gamma 0 = L.basepoint ∧
      ∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t| := by
  let _ : ConnectedSpace F.M := hK.connected
  have hzero : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have hcompleteSource : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hK.complete 0 hzero⟩
  have hsecSource : ∀ y : F.M, metricRm04At (I := I) (F.S.base.metric 0) y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := F.M) := by
    intro y
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (F.S.base.metric 0) y).mpr
    intro v w
    have h := hK.nonnegativeCurvatureOperator 0 hzero y 1
      (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [Fin.sum_univ_one, one_mul, SolutionFamily.rm04,
      metricRm04_apply, metricRm04StandardAt_apply, vec4] using h
  exact terminalLine_of_exact_sequence (F.S.base.metric 0) hcompleteSource hsecSource
    p x (fun i => Real.sqrt (F.S.scalar 0 (x i))) (fun i => Real.sqrt_pos.mpr (hQ i))
    (terminalCurvatureNormalizedFlowSeq_atZero_eq F hK x hQ)
    hescape hscaled hpsi Phi C hreference hcomplete hconnected

theorem exists_null_plane_of_terminalCurvatureNormalizedFlowSeq_limit
    {kappa : ℝ} (hK : KLim kappa F) (hdim : 2 ≤ Module.finrank ℝ E)
    (p : F.M) (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hescape : Tendsto
      (fun i => (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
      (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal) atTop atTop)
    {psi : ℕ → ℕ} (hpsi : StrictMono psi)
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) L psi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k =
      CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (hconnected : ConnectedSpace L.M)
    (q : L.M) :
    ∃ a b : TangentSpace I q,
      0 < L.metric.inner q a a * L.metric.inner q b b -
        (L.metric.inner q a b) ^ 2 ∧
          metricRm04StandardAt (I := I) L.metric q a b b a = 0 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace L.M := hconnected
  obtain ⟨gamma, -, hline⟩ := exists_line_of_terminalCurvatureNormalizedFlowSeq_limit
    F hK p x hQ hescape hscaled hpsi Phi C hreference hcomplete hconnected
  have hC : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi :=
    funext hcanonical
  have hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2 := by
    intro K hKc
    have h := C.converges K hKc 2
    rw [hC] at h
    exact h
  have hsecSeq : ∀ i : ℕ, ∀ y : F.M,
      let g : SmoothRiemannianMetric I F.M :=
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      metricRm04At (I := I) g y ∈
        tensor04SectionalNonnegativeCone (I := I) (M := F.M) := by
    intro i y
    let g : SmoothRiemannianMetric I F.M :=
      scaleMetric (F.S.scalar 0 (x i)) (hQ i)
        (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0))
    change metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := F.M)
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := I) g y).mpr
    intro v w
    dsimp only [g]
    rw [parabolicTime_zero, metricRmStandard_scale]
    apply mul_nonneg (hQ i).le
    have hzero : (0 : ℝ) ∈ D.carrier := by
      simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
    have h := hK.nonnegativeCurvatureOperator 0 hzero y 1
        (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [Fin.sum_univ_one, one_mul, SolutionFamily.rm04,
      metricRm04_apply, metricRm04StandardAt_apply, vec4] using h
  have hsec : ∀ q : L.M, metricRm04At (I := I) L.metric q ∈
      tensor04SectionalNonnegativeCone (I := I) (M := L.M) := by
    apply sectional_nonnegative_of_pointed_canonical_convergence hconv
    exact Filter.Eventually.of_forall (fun k y _ => hsecSeq (psi k) (Phi.map k y))
  exact exists_null_plane_of_nonnegative_sectional_intrinsic_line L.metric
    ⟨MetricComplete.complete L hcomplete⟩ hdim hsec hline q

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
