import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallWindow

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem boundedAtDistance_of_terminalParabolicRmBallBoundAtSameTime
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {start : ℝ} (hstart : start ≤ 0)
    (h : ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBoundAtSameTime X start ρ) :
    BoundedAtDistance X :=
  boundedAtDistance_of_terminalRmBallBound X fun ρ hρ => by
    obtain ⟨C, hC, hb⟩ := h ρ hρ
    refine ⟨C, hC, fun i t ht y hy => ?_⟩
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    exact hb i 0 ⟨hstart, le_rfl⟩ y hy

theorem bounded_curvature_at_distance_of_terminalRmBallBoundAtSameTimeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X := by
  obtain ⟨e, he, hb⟩ := h
  refine ⟨e, he, ?_⟩
  intro eps hp hle X
  refine boundedAtDistance_of_terminalParabolicRmBallBoundAtSameTime X ?_ (hb eps hp hle X)
  have hm : 0 < modelDepth eps := by
    simp only [modelDepth]
    exact inv_pos.mpr hp
  linarith

theorem bounded_curvature_at_distance_of_terminalParabolicRmBallWindowProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalParabolicRmBallWindowProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_terminalDerivativeBoundProducer
    (terminalDerivativeBoundProducer_of_terminalParabolicRmBallWindowProducer h)

theorem
 bounded_curvature_at_distance_of_terminalRmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_terminalDerivativeBoundProducer
    (terminalDerivativeBoundProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
      hrm hric)

theorem terminalDerivativeBoundProducer_of_bounded_curvature_at_distance
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X => (hb eps hp hle X).2⟩

theorem bounded_curvature_at_distance_of_parabolic_scalar_ball_and_ricci_bounds
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscl : TerminalScalarBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨K, hK, hric⟩ := hric
  exact bounded_curvature_at_distance_of_scalarBallBoundAtSameTime_and_ricciTensorBound
    hPhi hK hscl hric

theorem bounded_curvature_at_distance_iff_terminalDerivativeBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    (∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X) ↔
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi :=
  ⟨terminalDerivativeBoundProducer_of_bounded_curvature_at_distance,
    bounded_curvature_at_distance_of_terminalDerivativeBoundProducer⟩

theorem standardRmNormSq3_roundCylinder_scalar_one :
    standardRmNormSq3 (standardRmDiag3 (1 / 2) (1 / 2) 0) = 1 := by
  rw [standardRmNormSq3_diag]
  norm_num [rmSecNormSq3, sec12Ric3, sec13Ric3, sec23Ric3]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
