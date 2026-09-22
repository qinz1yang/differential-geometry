import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointBufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardSlabConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RemotePointTriangle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedOpenPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceScalarTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingSeparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseGeometry
import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FarPointSeparatingNeck

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}





theorem good_point_derivatives {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar C : ℝ, 0 < epsStar ∧ 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → interior D.carrier ⊆ D.regular →
          ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ x t, Nonempty (WindowedModelWitness eps kappa S x t) →
            (∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
              2 * C * S.scalar t x * Real.sqrt (S.scalar t x) *
                Real.sqrt ((S.base.metric t).inner x v v)) ∧
            |derivWithin (fun s => S.scalar s x) (Set.Iic t) t| ≤ C * S.scalar t x ^ 2 := by
  exact good_point_derivatives_of_modelCurvatureBound
    (KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
      (I := I3) (by simp [ThreeSpace]) hkappa)

theorem local_propagation {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar c C : ℝ, 0 < epsStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
            ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z : (X.term i).M,
              let L := 1 + |(X.term i).S.scalar s z|
              Set.Icc (s - c / L) s ⊆ (X.interval i).carrier ∧
                ∀ y v, (y, v) ∈ frozenBackwardCylinder (X.term i).S z s c c L →
                  -6 * (X.scale i)⁻¹ * Phi 0 ≤ (X.term i).S.scalar v y ∧
                  (X.term i).S.scalar v y ≤ 4 * L ∧
                  Real.sqrt (FlowMetricBall.rmNormSq (X.term i).S v y) ≤
                    C * (L + (Phi (4 * X.scale i * L) + Phi 0) / X.scale i) := by
  exact canonical_neighborhood_local_propagation hkappa


theorem first_backward_slab {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  exact exists_backward_extension_of_model_curvature_bound
    (KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
      (I := I3) (by simp [ThreeSpace]) hkappa) hsigma hPhi


theorem uniform_moving_slice_propagation {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ z y : L.space.M,
            B.solution.scalar s z ≤ A →
            metricDistance (B.solution.base.metric s) z y ≤ D →
              B.solution.scalar s y ≤ C := by
  exact uniform_moving_slice_propagation_of_recenteredSourceBound
    (recentered_source_bound hkappa hsigma hPhi)

theorem far_point_separating_neck {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (J : RealTimeInterval) (B : BackwardExtension L J),
        ¬ CompactSpace L.space.M → ∀ D : ℝ, 0 ≤ D →
        (∀ s ∈ J.carrier, ∀ y z : L.space.M,
          |metricDistance (B.solution.base.metric s) y z -
            metricDistance L.space.metric y z| ≤ D) →
        ∀ p : L.space.M, ∃ alpha D0 C0 : ℝ, 0 < alpha ∧ alpha < 1 / 11 ∧
          0 < D0 ∧ 0 < C0 ∧ ∀ s ∈ J.carrier, ∀ y : L.space.M,
            D0 < metricDistance L.space.metric p y →
            C0 < B.solution.scalar s y →
            ∃ (neck : SpatialNeck (B.solution.base.metric s) alpha y) (z : L.space.M),
              metricDistance L.space.metric p y <
                metricDistance L.space.metric p z ∧
              p ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)) ∧
              z ∉ connectedComponentIn (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ p ∧
              ∀ v ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                ∀ w ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                  metricDistance (B.solution.base.metric s) v w ≤
                    C0 / Real.sqrt (B.solution.scalar s y) := by
  obtain ⟨eps0, heps0, hmain⟩ := exists_far_point_separating_neck.{u} kappa
  let epsStar := min eps0 (min kappa (min sigma (Phi 0)))
  refine ⟨epsStar, lt_min heps0 (lt_min hkappa (lt_min hsigma (hPhi.pos 0))), ?_⟩
  intro eps _ heps X L J B hnoncompact D hD hdist p
  exact hmain (heps.trans (min_le_left eps0 (min kappa (min sigma (Phi 0)))))
    X L J B hnoncompact D hD hdist p



theorem ancient_extension_of_frontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
        HalfLineAnalyticInputs B) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
          Nonempty (AncientExtension B) := by
  obtain ⟨epsStar, hpos, hI⟩ := h
  exact ⟨epsStar, hpos, fun eps heps hle X L delta hd B =>
    ancientExtension_of_halfLine B (hI eps heps hle X L delta hd B)⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
