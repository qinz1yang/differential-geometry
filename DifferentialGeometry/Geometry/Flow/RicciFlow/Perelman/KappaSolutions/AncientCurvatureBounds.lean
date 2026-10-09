import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem rmNorm_le_scalar {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    PointedFlowRmNormLeScalar (I := I) F ((Module.finrank ℝ E : ℝ) ^ 2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro t ht x
  have hoperator :
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t ht x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hbound := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
    (F.S.base.metric t) x hoperator
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply, SolutionOn.scalar, SolutionFamily.scalar] using hbound

theorem exists_rmNormSq_le {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, ∀ t ∈ D.carrier, ∀ x : F.M,
      normSq0S (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ K := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2, ?_⟩
  intro t ht x
  have hle := hF.rmNorm_le_scalar t ht x
  have hscalar : F.S.scalar t x ≤ C := (hC t ht x).2
  have hsqrt : Real.sqrt (F.rmNormSq (I := I) t x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * C :=
    hle.trans (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _))
  have hnonneg : 0 ≤ F.rmNormSq (I := I) t x := by
    simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
      normSq0S_nonneg (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
  have hsq : Real.sqrt (F.rmNormSq (I := I) t x) ^ 2 = F.rmNormSq (I := I) t x :=
    Real.sq_sqrt hnonneg
  have hfinal : F.rmNormSq (I := I) t x ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (F.rmNormSq (I := I) t x)]
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply] using hfinal

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution
