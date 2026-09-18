import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSqrtLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalPoleCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance backwardCenterTopology : TopologicalSpace F.M := F.topology
private local instance backwardCenterCharted : ChartedSpace H F.M := F.charted
private local instance backwardCenterSmooth : IsManifold I ∞ F.M := F.smooth
private local instance backwardCenterT2 : T2Space F.M := F.t2
private local instance backwardCenterSigma : SigmaCompactSpace F.M := F.sigmaCompact

open DifferentialGeometry.Geometry.Curvature (metricScalarAt) in
theorem exists_backward_slice_centers_with_scalar_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) :
    ∃ q : ℕ → F.M,
      (∀ i, redLength F.S 0 p (q i) (tau i) ≤ (Module.finrank ℝ E : ℝ) / 2) ∧
      ∀ R : ℝ, 0 ≤ R → ∀ i : ℕ, ∀ x : F.M,
        riemannianEDistOf ((backwardSliceSequence F tau htau q).obj i).metric (q i) x ≤
          ENNReal.ofReal R →
        metricScalarAt (I := I) ((backwardSliceSequence F tau htau q).obj i).metric x ≤
          3 * (Real.sqrt ((Module.finrank ℝ E : ℝ) / 2) + Real.sqrt 3 / 2 * R) ^ 2 := by
  classical
  choose q hq using fun i => exists_redLength_le_half_finrank_of_ancient F hF p (htau i)
  refine ⟨q, hq, ?_⟩
  intro R hR i x hx
  rw [backwardSliceSequence_scalar]
  exact scalar_le_of_rescaled_distance_le F hF p (q i) x (htau i) hR (hq i) hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
