import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem boundedAtDistance_of_terminalRmBallBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X 0 ρ) : BoundedAtDistance X := by
  intro rho hrho
  obtain ⟨C, hCpos, hC⟩ := h rho hrho
  refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C, fun i y hy => ?_⟩
  have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
  have hed : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
      (X.term i).basepoint y ≤ ENNReal.ofReal rho :=
    (ENNReal.le_ofReal_iff_toReal_le
      (riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric 0)
        (X.term i).basepoint y) hrho.le).mpr (by simpa only [metricDistance] using hy)
  have hrm : Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ C := by
    have hzero : curvCovDeriv (I := I3) (M := (X.term i).M)
        ((X.term i).S.base.metric 0) 0 = metricRm04 (I := I3) (M := (X.term i).M)
          ((X.term i).S.base.metric 0) := rfl
    have hz := hC i 0 ⟨le_rfl, le_rfl⟩ y hed
    rwa [curvDerivNormSq, hzero, metricRm04_apply] at hz
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  have hscalar := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
    (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric 0) y
  rw [hdim] at hscalar
  calc (X.term i).S.scalar 0 y
      ≤ |metricScalarAt (I := I3) ((X.term i).S.base.metric 0) y| := le_abs_self _
    _ ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
            (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y)) := hscalar
    _ ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)

theorem terminalRmBallBound_at_zero_of_terminalDerivativeBounds
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : TerminalDerivativeBounds X) :
    ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X 0 ρ := by
  intro ρ hρ
  obtain ⟨C, hC⟩ := h ρ hρ 0
  refine ⟨max (max C 0 ^ 2) 1, lt_max_of_lt_right one_pos, fun i t ht y hy => ?_⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst ht0
  have hsq : curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric 0) y =
      curvDerivNorm (I := I3) 0 ((X.term i).S.base.metric 0) y ^ 2 := by
    rw [curvDerivNorm, Real.sq_sqrt]
    rw [curvDerivNormSq]
    exact Tensor0SBundle.normSq0S_nonneg (I := I3) ((X.term i).S.base.metric 0) y 4 _
  have hdist : metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ ρ := by
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
    simpa only [metricDistance, ENNReal.toReal_ofReal hρ.le] using hmono
  rw [hsq]
  calc curvDerivNorm (I := I3) 0 ((X.term i).S.base.metric 0) y ^ 2
      ≤ max C 0 ^ 2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_trans (hC i y hdist) (le_max_left _ _)) 2
    _ ≤ max (max C 0 ^ 2) 1 := le_max_left _ _

theorem boundedAtDistance_of_terminalDerivativeBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : TerminalDerivativeBounds X) :
    BoundedAtDistance X :=
  boundedAtDistance_of_terminalRmBallBound X
    (terminalRmBallBound_at_zero_of_terminalDerivativeBounds X h)

theorem bounded_curvature_at_distance_of_terminalDerivativeBounds
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, TerminalDerivativeBounds X) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X => ⟨boundedAtDistance_of_terminalDerivativeBounds X (hb eps hp hle X),
    hb eps hp hle X⟩⟩

abbrev TerminalDerivativeBoundProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, TerminalDerivativeBounds X

theorem bounded_curvature_at_distance_of_terminalDerivativeBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalDerivativeBoundProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  bounded_curvature_at_distance_of_terminalDerivativeBounds h

theorem terminalDerivativeBoundProducer_of_terminalParabolicCurvatureBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalParabolicCurvatureBoundProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨e, he, hg⟩ := bounded_curvature_at_distance_of_terminalParabolicCurvatureBoundProducer h
  exact ⟨e, he, fun eps hp hle X => (hg eps hp hle X).2⟩

theorem bounded_curvature_at_distance_of_terminalRmBallBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ∀ ρ : ℝ, 0 < ρ → TerminalParabolicRmBallBound X 0 ρ) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X => boundedAtDistance_of_terminalRmBallBound X (hb eps hp hle X)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
