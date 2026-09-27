import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ModelChange
import DifferentialGeometry.Geometry.Metric.ModelChange.PullbackIdentities
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence


noncomputable section

universe u uE uF uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private theorem metricDerivNormSupOn_model_change
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (e : E ≃L[ℝ] F) (K : Set M) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn (I := I.transContinuousLinearEquiv e) K p
        (gk.transContinuousLinearEquiv e) (gInf.transContinuousLinearEquiv e)
        (gRef.transContinuousLinearEquiv e) =
      metricDerivNormSupOn (I := I) K p gk gInf gRef := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  change metricDerivNormSupOn (I := I.transContinuousLinearEquiv e) K p
      (Diffeomorph.pullbackMetricCross gk
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm)
      (Diffeomorph.pullbackMetricCross gInf
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm)
      (Diffeomorph.pullbackMetricCross gRef
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm) = _
  rw [PDE.RicciFlow.Perelman.KappaSolutions.metricDerivNormSupOn_pullbackCross_image]
  change metricDerivNormSupOn (I := I) ((id : M → M) '' K) p gk gInf gRef = _
  rw [Set.image_id]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

theorem canonicalSourceData_derivNormSupOn_transContinuousLinearEquiv
    (Phi : PointedRiemannianConvergenceMaps X P phi) (e : E ≃L[ℝ] F)
    (k : ℕ) (K : Set P.M) (p : ℕ) :
    (CanonicalMetricCompactness.canonicalSourceData
        (Phi.transContinuousLinearEquiv e) k).derivNormSupOn K p =
      (CanonicalMetricCompactness.canonicalSourceData Phi k).derivNormSupOn K p := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let J := I.transContinuousLinearEquiv e
  let Psi := Phi.transContinuousLinearEquiv e
  let U : TopologicalSpace.Opens P.M := metricSourceOpenSubset Phi k
  let V : TopologicalSpace.Opens (X.obj (phi k)).M := metricTargetOpenSubset Phi k
  let _ : SigmaCompactSpace U := metric_source_domain_sigma_compact Phi k
    (Phi.isSigmaCompact_source k)
  let old : SmoothRiemannianMetric I V := (X.obj (phi k)).metric.restrictOpen V
  let d : U ≃ₘ⟮I, I⟯ V := metricSourceTargetDiffeomorph Phi k
  let d' : U ≃ₘ⟮J, J⟯ V := metricSourceTargetDiffeomorph Psi k
  have hd : (d' : U → V) = d := by
    funext x
    rfl
  change metricDerivNormSupOn (I := J) (Subtype.val ⁻¹' K : Set U) p
      (Diffeomorph.pullbackMetric
        (((X.obj (phi k)).metric.transContinuousLinearEquiv e).restrictOpen V) d')
      ((P.metric.transContinuousLinearEquiv e).restrictOpen U)
      ((P.metric.transContinuousLinearEquiv e).restrictOpen U) =
    metricDerivNormSupOn (I := I) (Subtype.val ⁻¹' K : Set U) p
      (Diffeomorph.pullbackMetric old d)
      (P.metric.restrictOpen U) (P.metric.restrictOpen U)
  rw [SmoothRiemannianMetric.transContinuousLinearEquiv_restrictOpen
      (X.obj (phi k)).metric e V,
    SmoothRiemannianMetric.transContinuousLinearEquiv_restrictOpen P.metric e U,
    ← SmoothRiemannianMetric.transContinuousLinearEquiv_pullbackMetric old e d d' hd]
  exact metricDerivNormSupOn_model_change e (Subtype.val ⁻¹' K : Set U) p _ _ _

theorem MetricConvergenceData.exists_transContinuousLinearEquiv
    (Phi : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (e : E ≃L[ℝ] F) :
    ∃ C' : MetricConvergenceData (Phi.transContinuousLinearEquiv e),
      (∀ k, C'.domain k = CanonicalMetricCompactness.canonicalSourceData
        (Phi.transContinuousLinearEquiv e) k) ∧
      (∀ k,
        let D := C'.domain k
        letI : TopologicalSpace
          (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D.topology
        letI : ChartedSpace H
          (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D.charted
        letI : IsManifold (I.transContinuousLinearEquiv e) ∞
          (MetricSourceDomain (Phi.transContinuousLinearEquiv e) k) := D.smooth
        D.referenceMetric = D.limitMetric) := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  apply exists_metricConvergenceData_canonicalSourceData (Phi.transContinuousLinearEquiv e)
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := C.converges K hK p epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  rw [canonicalSourceData_derivNormSupOn_transContinuousLinearEquiv Phi e k K p]
  have h := (hN k hk).2
  rwa [hcanonical k] at h

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
  exact MetricConvergenceData.exists_transContinuousLinearEquiv Phi C hC e

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
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply exists_metricConvergenceData_canonicalSourceData (Phi.ofTransContinuousLinearEquiv e)
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := C.converges K hK p epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  have h := (hN k hk).2
  rw [hC k] at h
  have heq := canonicalSourceData_derivNormSupOn_transContinuousLinearEquiv
    (Phi.ofTransContinuousLinearEquiv e) e k K p
  exact heq.symm.trans_lt h


end DifferentialGeometry.CheegerGromovCompactness
