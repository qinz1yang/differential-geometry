import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelFrontiers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureBlowupFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapMainFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaReducedVolumeBound

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem ancientModelClassificationDichotomy_of_reducedVolumeBound
    (h : AncientKappaReducedVolumeBound.{u, 0, 0} (I := I3)) :
    AncientModelClassificationDichotomy.{u} := by
  intro kappa _ P hP
  exact ancientKappaUniversalKappaGap_of_reducedVolumeBound (I := I3)
    (by simp [ThreeSpace]) h kappa P hP

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem kappaUniformCanonicalClassification_of_reducedVolumeBound_modelBranches
    (hred : AncientKappaReducedVolumeBound.{u, 0, 0} (I := I3))
    (hbranches : ModelCanonicalWitnessBranches.{u})
    (htransfer : ∀ (eps C1 C2 kappa : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
      (x : M) (t : ℝ) (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    kappaUniformCanonicalClassification.{u} :=
  kappaUniformCanonicalClassification_of_modelBranches
    (ancientModelClassificationDichotomy_of_reducedVolumeBound hred) hbranches htransfer

theorem buffered_canonical_pullback_of_reducedVolumeBound_modelBranches
    (hred : AncientKappaReducedVolumeBound.{u, 0, 0} (I := I3))
    (hbranches : ModelCanonicalWitnessBranches.{u})
    (htransfer : ∀ (eps C1 C2 kappa : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
      (x : M) (t : ℝ) (W : WindowedModelWitness (1 / 2) kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
          ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
            [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
            (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
            (o : TangentOrientationSection M) (x : M) (t : ℝ),
            OrientedWitness S o delta kappa x t → Nonempty (CanonicalWitness S eps C1 C2 x t) :=
  buffered_canonical_pullback_of_classification
    (kappaUniformCanonicalClassification_of_reducedVolumeBound_modelBranches
      hred hbranches htransfer)

theorem arbitrary_high_curvature_blowup_of_maximalPointSlabCompactnessWithoutBaseNormalization
    [CompactSpace M] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : MaximalPointSlabCompactnessWithoutBaseNormalization.{u} hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ico 0 T) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        Nonempty (BlowupLimit S o kappa x t) :=
  arbitrary_high_curvature_blowup_of_blowupAtHighCurvatureFrontier hT S o
    (blowupAtHighCurvatureFrontier_of_maximalPointSlabCompactness hT S hS o
      (maximalPointSlabCompactness_of_withoutBaseNormalization hT S hS o h))

omit [T2Space M] [SigmaCompactSpace M] in
theorem blowupAtHighCurvatureFrontier_of_forall_scalar_eq_zero
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (o : TangentOrientationSection M)
    (hscalar : ∀ (t : ℝ) (x : M), S.scalar t x = 0) :
    BlowupAtHighCurvatureFrontier.{u} hT S o := by
  refine ⟨1, one_pos, fun x t _ htendsto => ?_⟩
  have hge : ∀ᶠ i : ℕ in Filter.atTop, (1 : ℝ) < S.scalar (t i) (x i) :=
    htendsto.eventually (Filter.eventually_gt_atTop 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hge
  have hN' := hN N le_rfl
  rw [hscalar (t N) (x N)] at hN'
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
