import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckDetection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckScaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalNeckSourceTopology : TopologicalSpace F.M := F.topology
private local instance terminalNeckSourceCharted : ChartedSpace H F.M := F.charted
private local instance terminalNeckSourceSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalNeckSourceT2 : T2Space F.M := F.t2
private local instance terminalNeckSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance terminalNeckLimitTopology : TopologicalSpace G.M := G.topology
private local instance terminalNeckLimitCharted : ChartedSpace H G.M := G.charted
private local instance terminalNeckLimitSmooth : IsManifold I ∞ G.M := G.smooth
private local instance terminalNeckLimitT2 : T2Space G.M := G.t2
private local instance terminalNeckLimitSigma : SigmaCompactSpace G.M := G.sigmaCompact

theorem terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness
    {kappa : ℝ} (hK : KLim kappa F) (hG : IsAncientKappaSolution (I := I) kappa G)
    (hdim : Module.finrank ℝ E = 3)
    (p : F.M) (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hescape : Tendsto
      (fun i => (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
      (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal) atTop atTop)
    {psi : ℕ → ℕ} (hpsi : StrictMono psi)
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) (G.atTime 0) psi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k =
      CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k)
    (hEuclidean : Nonempty (F.M ≃ₘ⟮I, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3))) :
    ∃ (yStar : SpatialNeckSphere)
      (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ G.M),
      e (yStar, 0) = G.basepoint ∧
      Diffeomorph.pullbackMetricCross (G.S.family.metric 0) e = doubleSphereCylinderMetric ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ W : SpatialNeckWitness (F.S.base.metric 0) yStar (x (psi k)) epsilon,
          ∀ z : spatialNeckBuffer epsilon,
            W.embedding z = Phi.map k
              (e (cylinderAxialScale (Real.sqrt 2) (by positivity)
                (z : SpatialNeckCylinder))) := by
  obtain ⟨T, hT, d, hproduct⟩ :=
    exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit
      F G hK hG hdim p x hQ hescape hscaled hpsi Phi C hcanonical hEuclidean
  have hscalar :=
    terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one F hK x hQ Phi C hcanonical
  change metricScalarAt (I := I) (G.S.family.metric 0) G.basepoint = 1 at hscalar
  obtain ⟨yStar, e, hmarked, hmetric, _⟩ := exists_marked_normalized_cylinder
    G.S.family.metric T hT d hproduct G.basepoint hscalar
  refine ⟨yStar, e, hmarked, hmetric, ?_⟩
  intro epsilon hepsilon
  obtain ⟨k0, hk0⟩ := pointedCylinderLimit_eventually_spatialNeckWitness
    Phi C hcanonical hdim
    (fun k => (terminalCurvatureNormalizedFlowSeq_complete F hK x hQ).complete_on
      k 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ)
    yStar e hmarked hmetric epsilon hepsilon
  refine ⟨k0, fun k hk => ?_⟩
  have hscaledWitness :
      ∃ W : SpatialNeckWitness
          (scaleMetric (F.S.scalar 0 (x (psi k))) (hQ (psi k)) (F.S.base.metric 0))
          yStar (x (psi k)) epsilon,
        ∀ z : spatialNeckBuffer epsilon,
          W.embedding z = Phi.map k
            (e (cylinderAxialScale (Real.sqrt 2) (by positivity)
              (z : SpatialNeckCylinder))) := by
    rw [← terminalCurvatureNormalizedFlowSeq_metric F hK x hQ (psi k)]
    exact hk0 k hk
  obtain ⟨W, hW⟩ := hscaledWitness
  exact ⟨W.ofScaleMetric (F.S.scalar 0 (x (psi k))) (hQ (psi k)), hW⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
