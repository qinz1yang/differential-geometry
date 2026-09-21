import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance pointedScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedScalarLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedScalarLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedScalarLimitT2 : T2Space L.M := L.t2
local instance pointedScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
local instance pointedScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

variable {Phi}

theorem pointedScalar_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (x : L.M) :
    Tendsto (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      atTop (𝓝 (metricScalarAt (I := I) L.metric x)) := by
  exact (pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence
    isCompact_singleton (hconv {x} isCompact_singleton)).tendsto_at (mem_singleton x)

theorem pointedScalar_tendsto_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (x : L.M) :
    Tendsto (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      atTop (𝓝 (metricScalarAt (I := I) L.metric x)) := by
  apply pointedScalar_tendsto_of_canonical_metric_convergence
  intro K hK
  have ht := C.converges K hK 2
  have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
  rw [hD] at ht
  exact ht

theorem pointedScalar_base_eq_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    {c : ℝ}
    (hbase : ∀ k, metricScalarAt (I := I) (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint = c) :
    metricScalarAt (I := I) L.metric L.basepoint = c := by
  have hc := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical L.basepoint
  have heq : (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric
      (Phi.map k L.basepoint)) = fun _ : ℕ => c := by
    funext k
    have hmap : Phi.map k L.basepoint = (X.obj (subseq k)).basepoint :=
      Phi.basepoint_map k
    rw [hmap]
    exact hbase k
  rw [heq] at hc
  exact tendsto_nhds_unique hc tendsto_const_nhds

theorem scalar_base_eq_in_canonicalMetricCompactness
    (C : CanonicalMetricCompactness (I := I) X) {c : ℝ}
    (hbase : ∀ k,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let _ : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let _ : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let _ : T2Space (X.obj k).M := (X.obj k).t2
      metricScalarAt (I := I) (X.obj k).metric (X.obj k).basepoint = c) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    metricScalarAt (I := I) P.metric P.basepoint = c :=
  pointedScalar_base_eq_of_metricCG_canonical_domains C.compactness.convergence.metrics
    C.domain_eq_canonical (fun k => hbase (C.compactness.subseq k))

section NormalizedTerminalSequence

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance pointedScalarFlowTopology : TopologicalSpace F.M := F.topology
local instance pointedScalarFlowCharted : ChartedSpace H F.M := F.charted
local instance pointedScalarFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance pointedScalarFlowT2 : T2Space F.M := F.t2
local instance pointedScalarFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) L subseq)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) :
    metricScalarAt (I := I) L.metric L.basepoint = 1 := by
  apply pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical
  intro k
  exact terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ (subseq k)

theorem terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (C : CanonicalMetricCompactness (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I))) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    metricScalarAt (I := I) P.metric P.basepoint = 1 :=
  scalar_base_eq_in_canonicalMetricCompactness C
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ)

end NormalizedTerminalSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
