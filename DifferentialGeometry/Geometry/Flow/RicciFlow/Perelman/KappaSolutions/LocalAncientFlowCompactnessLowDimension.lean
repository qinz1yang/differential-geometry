import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalAncientFlowCompactnessReduction

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem metricRm04_eq_zero_of_finrank_le_one (g : SmoothRiemannianMetric I M)
    (hE : Module.finrank ℝ E ≤ 1) :
    metricRm04 (I := I) (M := M) g = 0 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricRm04_apply]
  exact metricRm04At_eq_zero_of_finrank_le_one (I := I) g hE x

omit [SigmaCompactSpace M] in
theorem curvCovDeriv_eq_zero_of_finrank_le_one (g : SmoothRiemannianMetric I M)
    (hE : Module.finrank ℝ E ≤ 1) (k : ℕ) :
    curvCovDeriv (I := I) (M := M) g k = 0 := by
  induction k with
  | zero => exact metricRm04_eq_zero_of_finrank_le_one (I := I) g hE
  | succ k ih => rw [curvCovDeriv_succ, ih, curvStep_eq_covStep, covStep_zero]

omit [SigmaCompactSpace M] in
theorem curvDerivNorm_eq_zero_of_finrank_le_one (g : SmoothRiemannianMetric I M)
    (hE : Module.finrank ℝ E ≤ 1) (k : ℕ) (x : M) :
    curvDerivNorm (I := I) k g x = 0 := by
  rw [curvDerivNorm, curvDerivNormSq]
  have hcomp : curvCovDeriv (I := I) (M := M) g k x = 0 := by
    rw [curvCovDeriv_eq_zero_of_finrank_le_one (I := I) g hE k]
    rfl
  rw [hcomp, (Tensor0SBundle.normSq0S_eq_zero_iff (I := I) g x (k + 4) 0).mpr rfl,
    Real.sqrt_zero]

end CheegerGromovCompactness

namespace PDE
namespace RicciFlow
namespace Perelman
namespace KappaSolutions

open Bundle Filter
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem ancientZeroBallJetBound_of_finrank_le_one
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hE : Module.finrank ℝ E ≤ 1) :
    AncientZeroBallJetBound (I := I) X := by
  refine ⟨fun A _hA p => ⟨0, le_rfl, ?_⟩⟩
  refine Filter.Eventually.of_forall fun i => ?_
  exact
    let _ : TopologicalSpace (X.term i).M := (X.term i).topology
    let _ : ChartedSpace H (X.term i).M := (X.term i).charted
    let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    let _ : T2Space (X.term i).M := (X.term i).t2
    let _ : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    fun x _ => by
      rw [curvDerivNorm_eq_zero_of_finrank_le_one (I := I)
        ((X.term i).S.base.metric 0) hE p x]

theorem exists_local_ancient_flow_compactness_of_metricCompactSeedFrontier_and_limitExtension
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      ConnectedSpace (X.term i).M)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M,
          riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
              (X.term i).basepoint x ≤ ENNReal.ofReal A →
            (X.term i).rmNormSq (I := I) t x ≤ K)
    (hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.term i).M := (X.term i).topology
        let _ : ChartedSpace H (X.term i).M := (X.term i).charted
        let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
        ∀ t ∈ Set.Icc (-T) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I x,
          c * ((X.term i).S.base.metric 0).inner x v v ≤
            ((X.term i).S.base.metric t).inner x v v)
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y)
    (hext : ∀ P : MetricCompactLimit.{u, uE, uH} (I := I) (X.atZero (I := I)),
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) →
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) →
      ∃ (phi : ℕ → ℕ) (_ : StrictMono phi)
        (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
        (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi),
        AncientFlowLimitExtension (I := I) X P phi L Phi) :
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        (let _ : TopologicalSpace L.M := L.topology
         ConnectedSpace L.M) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k) ∧
            (∀ k,
              let D := C.domain k
              let _ : TopologicalSpace
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.topology
              let _ : ChartedSpace H
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.charted
              let _ : IsManifold I ∞
                (MetricSourceDomain (I := I) (Phi.atTime (L := L) t) k) := D.smooth
              D.referenceMetric = D.limitMetric) := by
  by_cases hE : Module.finrank ℝ E ≤ 1
  · exact exists_local_ancient_flow_compactness_of_frontier (I := I) X hD hcomplete hconnected
      hinj (ancientZeroBallJetBound_of_finrank_le_one (I := I) X hE) hseed hext
  · have h2 : 2 ≤ Module.finrank ℝ E := by omega
    exact exists_local_ancient_flow_compactness_of_local_curvature_bound_and_frontier (I := I) X
      hD hcomplete hconnected hinj h2 hlocal hlower hseed hext

end KappaSolutions
end Perelman
end RicciFlow
end PDE

end DifferentialGeometry
