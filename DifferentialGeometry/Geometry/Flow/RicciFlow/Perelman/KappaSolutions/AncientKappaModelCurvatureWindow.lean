import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle


theorem ancientKappa_modelCurvatureBoundNearBase (hdim : Module.finrank ℝ E = 3)
    {kappa : ℝ} (_hkappa : 0 < kappa) :
    ModelCurvatureBoundNearBase.{u, uE, uH} I kappa := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_klim_local_curvature_constants.{u, uE, uH} (I := I) hdim kappa
  refine ⟨Real.sqrt 3 * C 3, mul_nonneg (Real.sqrt_nonneg _) (hC 3).le, ?_⟩
  intro L hL hbase s hs y hy
  have hK : KLim kappa L := ancientKappaThree_toKLim L hL hdim
  have hb : L.S.scalar 0 L.basepoint = 1 := hbase
  have h := (hbound ancientTimeInterval L hK hb 3 y hy s hs.2).2
  calc L.rmNormSq (I := I) s y ≤ 3 * C 3 ^ 2 := h
    _ = (Real.sqrt 3 * C 3) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
