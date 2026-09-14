import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingSeparation

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation (TwoSidedSeparation)
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def FarPointSeparatingNeckInput (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
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
          ∃ (neck : SpatialNeck (B.solution.base.metric s) alpha y) (z : L.space.M)
            (c : TransversePath p z (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))))
            (d : TwoSidedSeparation (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))),
            metricDistance L.space.metric p y < metricDistance L.space.metric p z ∧
            p ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)) ∧
            z ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)) ∧
            (c.intersection = 1 ∨ c.intersection = -1) ∧
            ((p ∈ d.positiveSide ∧ z ∈ d.negativeSide) ∨
              (p ∈ d.negativeSide ∧ z ∈ d.positiveSide)) ∧
            ∀ v ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
              ∀ w ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                metricDistance (B.solution.base.metric s) v w ≤
                  C0 / Real.sqrt (B.solution.scalar s y)

theorem far_point_separating_neck_of_input {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : FarPointSeparatingNeckInput.{u} kappa sigma Phi) :
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
  obtain ⟨epsStar, hpos, hmain⟩ := h
  refine ⟨epsStar, hpos, fun eps heps hle X L J B hnc D hD hdist p => ?_⟩
  obtain ⟨alpha, D0, C0, ha, hasmall, hD0, hC0, hbody⟩ :=
    hmain eps heps hle X L J B hnc D hD hdist p
  refine ⟨alpha, D0, C0, ha, hasmall, hD0, hC0, fun s hs y hfar hhigh => ?_⟩
  obtain ⟨neck, z, c, d, hlt, hp, hz, hint, hsides, hdiam⟩ := hbody s hs y hfar hhigh
  have hcomp := c.not_mem_connectedComponentIn_of_intersection d hp hz hint
  refine ⟨neck, z, hlt, hp, ?_, hdiam⟩
  rcases hsides with _ | _
  · exact hcomp
  · exact hcomp


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
