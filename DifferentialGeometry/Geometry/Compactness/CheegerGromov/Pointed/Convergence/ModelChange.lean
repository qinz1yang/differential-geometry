import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.ModelChange
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ModelChange
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence

noncomputable section
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness
universe u uE uF uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

def PointedRiemannianConvergenceMaps.transContinuousLinearEquiv
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F) :
    PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi where
  partialDiffeomorph i := (Phi.partialDiffeomorph i).transContinuousLinearEquiv e e
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

namespace PointedRiemannianConvergenceMaps

variable {X : PointedRiemannianSeq.{u, uE, uH} I}
  {P : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}

omit [FiniteDimensional ℝ E] in
@[simp] theorem transContinuousLinearEquiv_source
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).source k = Phi.source k := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem transContinuousLinearEquiv_target
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).target k = Phi.target k := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem transContinuousLinearEquiv_map
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F) (k : ℕ) :
    (Phi.transContinuousLinearEquiv e).map k = Phi.map k := rfl

end PointedRiemannianConvergenceMaps

variable [CompleteSpace E] [CompleteSpace F]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem canonicalSourceData_derivNormSupOn_transContinuousLinearEquiv
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F)
    (k : ℕ) (K : Set P.M) (p : ℕ) :
    (CanonicalMetricCompactness.canonicalSourceData (Phi.transContinuousLinearEquiv e) k).derivNormSupOn K p =
      (CanonicalMetricCompactness.canonicalSourceData Phi k).derivNormSupOn K p := by
  let U := metricSourceOpenSubset Phi k
  let D := CanonicalMetricCompactness.canonicalSourceData Phi k
  let D' := CanonicalMetricCompactness.canonicalSourceData (Phi.transContinuousLinearEquiv e) k
  let _ : TopologicalSpace (MetricSourceDomain Phi k) := D.topology
  let _ : ChartedSpace H (MetricSourceDomain Phi k) := D.charted
  let _ : T2Space (MetricSourceDomain Phi k) := D.t2
  let _ : IsManifold I ∞ (MetricSourceDomain Phi k) := D.smooth
  let _ : SigmaCompactSpace (MetricSourceDomain Phi k) :=
    D.sigmaCompact
  let _ : TopologicalSpace (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D'.topology
  let _ : ChartedSpace H (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D'.charted
  let _ : T2Space (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D'.t2
  let _ : IsManifold (I.transContinuousLinearEquiv e) ∞ (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D'.smooth
  let _ : SigmaCompactSpace (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D'.sigmaCompact
  have hlim : D'.limitMetric = D.limitMetric.transContinuousLinearEquiv e := by
    change (P.metric.transContinuousLinearEquiv e).restrictOpen U =
      (P.metric.restrictOpen U).transContinuousLinearEquiv e
    exact P.metric.restrictOpen_transContinuousLinearEquiv e U
  let V := metricTargetOpenSubset Phi k
  let _ : TopologicalSpace (MetricTargetDomain Phi k) := metricTargetDomainTopology Phi k
  let _ : ChartedSpace H (MetricTargetDomain Phi k) := metricTargetDomainChartedSpace Phi k
  let _ : T2Space (MetricTargetDomain Phi k) := metric_target_domain_t2 Phi k
  let _ : IsManifold I ∞ (MetricTargetDomain Phi k) := metric_target_domain_smooth Phi k
  have hpull : D'.pullbackMetric = D.pullbackMetric.transContinuousLinearEquiv e := by
    have h := Diffeomorph.pullbackMetricCross_transContinuousLinearEquiv_of_coe_eq
      ((X.obj (phi k)).metric.restrictOpen V) e e
      (metricSourceTargetDiffeomorph Phi k)
      (metricSourceTargetDiffeomorph (Phi.transContinuousLinearEquiv e) k) rfl
    simp only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] at h
    have hg := (X.obj (phi k)).metric.restrictOpen_transContinuousLinearEquiv e V
    change Diffeomorph.pullbackMetric ((X.obj (phi k)).metric.transContinuousLinearEquiv e |>.restrictOpen V)
      (metricSourceTargetDiffeomorph (Phi.transContinuousLinearEquiv e) k) = _
    exact (congrArg (fun g => Diffeomorph.pullbackMetric g
      (metricSourceTargetDiffeomorph (Phi.transContinuousLinearEquiv e) k)) hg).trans h
  change metricDerivNormSupOn _ _ D'.pullbackMetric D'.limitMetric D'.referenceMetric =
    metricDerivNormSupOn _ _ D.pullbackMetric D.limitMetric D.referenceMetric
  erw [canonicalSourceData_referenceMetric_eq_limitMetric,
    canonicalSourceData_referenceMetric_eq_limitMetric, hlim, hpull]
  have h := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricDerivNormSupOn_pullbackCross_image
    (metricSourceCompactSet Phi k K) p D.pullbackMetric D.limitMetric D.limitMetric
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I U e).symm
  have hi : ((ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I U e).symm : U → U) = id := rfl
  rw [hi, Set.image_id] at h
  exact h


theorem exists_canonicalMetricConvergenceData_transContinuousLinearEquiv
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}
    {Phi : PointedRiemannianConvergenceMaps X P phi}
    (C : MetricConvergenceData Phi)
    (hC : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (e : E ≃L[ℝ] F) :
    ∃ C' : MetricConvergenceData (Phi.transContinuousLinearEquiv e),
      (∀ k, C'.domain k = CanonicalMetricCompactness.canonicalSourceData
        (Phi.transContinuousLinearEquiv e) k) ∧
      (∀ k, (C'.domain k).referenceMetric = (C'.domain k).limitMetric) := by
  apply exists_metricConvergenceData_canonicalSourceData
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := C.converges K hK p epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  have h := (hN k hk).2
  rw [hC k] at h
  exact (canonicalSourceData_derivNormSupOn_transContinuousLinearEquiv Phi e k K p).trans_lt h

variable {X : PointedRiemannianSeq.{u, uE, uH} I}
  {P : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}

def PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv (e : E ≃L[ℝ] F)
    (Phi : PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi) : PointedRiemannianConvergenceMaps X P phi where
  partialDiffeomorph k := (Phi.partialDiffeomorph k).ofTransContinuousLinearEquiv e e
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem PointedRiemannianConvergenceMaps.transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[ℝ] F)
    (Phi : PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi) :
    (Phi.ofTransContinuousLinearEquiv e).transContinuousLinearEquiv e = Phi := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem PointedRiemannianConvergenceMaps.ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F) :
    (Phi.transContinuousLinearEquiv e).ofTransContinuousLinearEquiv e = Phi := rfl


theorem exists_canonicalMetricConvergenceData_of_transContinuousLinearEquiv
    (e : E ≃L[ℝ] F)
    {Phi : PointedRiemannianConvergenceMaps (X.transContinuousLinearEquiv e)
      (P.transContinuousLinearEquiv e) phi}
    (C : MetricConvergenceData Phi)
    (hC : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) :
    ∃ C' : MetricConvergenceData (Phi.ofTransContinuousLinearEquiv e),
      (∀ k, C'.domain k = CanonicalMetricCompactness.canonicalSourceData
        (Phi.ofTransContinuousLinearEquiv e) k) ∧
      (∀ k, (C'.domain k).referenceMetric = (C'.domain k).limitMetric) := by
  apply exists_metricConvergenceData_canonicalSourceData
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := C.converges K hK p epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  have h := (hN k hk).2
  rw [hC k] at h
  have heq := canonicalSourceData_derivNormSupOn_transContinuousLinearEquiv
    (Phi.ofTransContinuousLinearEquiv e) e k K p
  exact heq.symm.trans_lt h


end DifferentialGeometry.CheegerGromovCompactness
