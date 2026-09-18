import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance compactnessTopology : TopologicalSpace F.M := F.topology
private local instance compactnessCharted : ChartedSpace H F.M := F.charted
private local instance compactnessSmooth : IsManifold I ∞ F.M := F.smooth
private local instance compactnessT2 : T2Space F.M := F.t2
private local instance compactnessSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem backwardSliceApproximateMetricCompactness_of_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) :
    backwardSliceApproximateMetricCompactness F hF tau htau q := by
  let X := backwardSliceSequence F tau htau q
  have hjets : ∀ R : ℝ, 0 < R → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop, HasLocalCurvDerivBound (I := I) (X.obj i) (X.obj i).basepoint R m C := by
    intro R hR m
    let K := 1 + (Module.finrank ℝ E : ℝ) ^ 2 *
      (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (R + 1)) ^ 2)
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    refine ⟨shiLocalUniformBound (Module.finrank ℝ E) m K (Real.sqrt K) * K,
      mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK, Eventually.of_forall ?_⟩
    intro i x hx
    exact curvDerivNorm_le_of_rescaled_distance_le F hF p (q i) x (htau i) hR.le (hbase i) hx m
  have hinj : ∀ R : ℝ, 0 < R → ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ i in atTop, ∀ x : (X.obj i).M,
        riemannianEDistOf (X.obj i).metric (X.obj i).basepoint x ≤ ENNReal.ofReal R →
        HasInjRadiusAt (I := I) (X.obj i) x eta := by
    intro R hR
    obtain ⟨eta, heta, hinj⟩ := exists_backwardSliceSequence_injRadius_bound F hF p tau htau q hbase hR.le
    exact ⟨eta, heta, Eventually.of_forall hinj⟩
  obtain ⟨phi, hphi, hpair⟩ :=
    exists_subsequence_pairwise_metric_approximation_of_local_curvature_injectivity_on_balls X
      (backwardSliceSequence_complete F hF tau htau q)
      (backwardSliceSequence_connected F hF tau htau q) hjets hinj
  refine ⟨phi, hphi, ?_⟩
  exact HasPairwiseApproximateIsometries.of_partial_metric_approximations (X.subseq phi)
    (fun k => properMetricOn (X.obj (phi k))
      ((backwardSliceSequence_complete F hF tau htau q).complete (phi k))
      (backwardSliceSequence_connected F hF tau htau q (phi k))) hpair

theorem exists_backward_slice_centers_with_approximate_metric_compactness
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) :
    ∃ q : ℕ → F.M,
      (∀ i, redLength F.S 0 p (q i) (tau i) ≤ (Module.finrank ℝ E : ℝ) / 2) ∧
      backwardSliceApproximateMetricCompactness F hF tau htau q := by
  classical
  choose q hq using fun i => exists_redLength_le_half_finrank_of_ancient F hF p (htau i)
  exact ⟨q, hq, backwardSliceApproximateMetricCompactness_of_redLength_le F hF p tau htau q hq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
