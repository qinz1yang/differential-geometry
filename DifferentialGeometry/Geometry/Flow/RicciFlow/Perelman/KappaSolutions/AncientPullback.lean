import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.PointedPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Pullback

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.PointedFlowData

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open Bundle
open scoped Manifold ContDiff

universe u v uE uH uE' uH'
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {H' : Type uH'} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {D : RealTimeInterval}
  (F : PointedFlowData.{v, uE', uH'} (I := J) D)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [local instance] pullbackTargetTopology pullbackTargetCharted
  pullbackTargetSmooth pullbackTargetT2 pullbackTargetSigmaCompact

theorem pullback_nonnegativeCurvatureOperator (Phi : M ≃ₘ⟮I, J⟯ F.M) (t : ℝ)
    (hF : PointedFlowNonnegativeCurvatureOperator F t) :
    PointedFlowNonnegativeCurvatureOperator (F.pullback Phi) t := by
  change ∀ (x : M) (n : ℕ) (c : Fin n → ℝ)
    (v w : Fin n → TangentSpace I x),
    0 ≤ ∑ i, ∑ j, c i * c j *
      metricRm04At (Diffeomorph.pullbackMetricCross (F.S.base.metric t) Phi) x
        (vec4 (v i) (w i) (w j) (v j))
  intro x n c v w
  have hh := hF (Phi x) n c
    (fun i => mfderiv I J (Phi : M → F.M) x (v i))
    (fun i => mfderiv I J (Phi : M → F.M) x (w i))
  have hcurv (a b c d : TangentSpace I x) :
      metricRm04At (Diffeomorph.pullbackMetricCross (F.S.base.metric t) Phi) x
        (vec4 a b c d) = metricRm04At (F.S.base.metric t) (Phi x)
          (vec4 (mfderiv I J Phi x a) (mfderiv I J Phi x b)
            (mfderiv I J Phi x c) (mfderiv I J Phi x d)) := by
    simpa only [metricRm04StandardAt_apply] using
      metricRm04Standard_pullbackCross (F.S.base.metric t) Phi x a b c d
  simpa only [hcurv, SolutionFamily.rm04, metricRm04_apply] using hh

theorem pullback_scalarBounded (Phi : M ≃ₘ⟮I, J⟯ F.M) (C : ℝ)
    (hF : PointedFlowScalarBounded F C) :
    PointedFlowScalarBounded (F.pullback Phi) C := by
  change ∀ t ∈ D.carrier, ∀ x : M, _
  intro t ht x
  change 0 ≤ (F.S.pullback Phi).scalar t x ∧ (F.S.pullback Phi).scalar t x ≤ C
  rw [SolutionOn.pullback_scalar]
  exact hF t ht (Phi x)

theorem pullback_notFlat (Phi : M ≃ₘ⟮I, J⟯ F.M)
    (hF : PointedFlowNotFlat F) : PointedFlowNotFlat (F.pullback Phi) := by
  obtain ⟨t, ht, x, hx⟩ := hF
  refine ⟨t, ht, Phi.symm x, ?_⟩
  simpa only [pullback_rmNormSq, Phi.apply_symm_apply] using hx

theorem pullback_noncollapsed (Phi : M ≃ₘ⟮I, J⟯ F.M) (kappa : ℝ)
    (hF : PointedFlowNoncollapsedAllScales F kappa) :
    PointedFlowNoncollapsedAllScales (F.pullback Phi) kappa := by
  change ∀ (time : D.FlowTime)
    (B : Perelman.FlowMetricBall (F.S.pullback Phi) time),
    B.IsSpatiallyKappaNoncollapsed kappa
  intro time B
  exact Perelman.FlowMetricBall.isSpatiallyKappaNoncollapsed_pullback F.S Phi (hF time) B

theorem pullback_isAncientKappaSolution (Phi : M ≃ₘ⟮I, J⟯ F.M) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    IsAncientKappaSolution kappa (F.pullback Phi) where
  kappa_pos := hF.kappa_pos
  carrier_eq := hF.carrier_eq
  regular_eq := hF.regular_eq
  connected := Phi.toHomeomorph.connectedSpace_iff.mpr hF.connected
  complete := fun t ht => F.pullback_complete Phi t (hF.complete t ht)
  nonnegativeCurvatureOperator := fun t ht =>
    F.pullback_nonnegativeCurvatureOperator Phi t (hF.nonnegativeCurvatureOperator t ht)
  globalScalarBound := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact ⟨C, F.pullback_scalarBounded Phi C hC⟩
  noncollapsed := F.pullback_noncollapsed Phi kappa hF.noncollapsed
  notFlat := F.pullback_notFlat Phi hF.notFlat

end DifferentialGeometry.CheegerGromovCompactness.PointedFlowData
