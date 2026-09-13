import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBallNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallAtSameTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedAtDistanceFromRmBallBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

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

def TerminalParabolicRmBallWindow {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start : ℝ) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∃ ρ : ℝ, 0 < ρ ∧
    TerminalParabolicRmBallBound X start (2 * ρ) ∧
    TerminalParabolicBallNesting X start rho ρ

theorem terminalParabolicRmBallWindow_iff_curvatureBound {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start : ℝ) :
    TerminalParabolicRmBallWindow X start ↔ TerminalParabolicCurvatureBound X start :=
  (terminalParabolicCurvatureBound_iff_scale_windows X start).symm

theorem terminalDerivativeBounds_of_terminalParabolicRmBallWindow
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (heps : 0 < eps) (h : TerminalParabolicRmBallWindow X (-(modelDepth eps))) :
    TerminalDerivativeBounds X :=
  terminalDerivativeBounds_of_parabolicCurvatureBounds X
    (parabolicCurvatureBoundsAtBase_of_terminalParabolicCurvatureControl X heps
      (terminalParabolicCurvatureControl_of_bound X heps
        ((terminalParabolicRmBallWindow_iff_curvatureBound X (-(modelDepth eps))).mp h)))

abbrev TerminalParabolicRmBallWindowProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      TerminalParabolicRmBallWindow X (-(modelDepth eps))

theorem terminalParabolicRmBallWindowProducer_iff_terminalParabolicCurvatureBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    TerminalParabolicRmBallWindowProducer.{u} kappa sigma Phi ↔
      TerminalParabolicCurvatureBoundProducer.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, hw⟩
    exact ⟨e, he, fun eps hp hle X =>
      (terminalParabolicRmBallWindow_iff_curvatureBound X (-(modelDepth eps))).mp
        (hw eps hp hle X)⟩
  · rintro ⟨e, he, hw⟩
    exact ⟨e, he, fun eps hp hle X =>
      (terminalParabolicRmBallWindow_iff_curvatureBound X (-(modelDepth eps))).mpr
        (hw eps hp hle X)⟩

theorem terminalDerivativeBoundProducer_of_terminalParabolicRmBallWindowProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalParabolicRmBallWindowProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨e, he, hw⟩ := h
  exact ⟨e, he, fun eps hp hle X =>
    terminalDerivativeBounds_of_terminalParabolicRmBallWindow X hp (hw eps hp hle X)⟩

def TerminalRmBallBoundAtZero {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → TerminalParabolicRmBallBound X 0 rho

def TerminalHigherDerivativeBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∀ rho : ℝ, 0 < rho → ∀ a : ℕ, 1 ≤ a → ∃ C : ℝ, ∀ i, ∀ y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      curvDerivNorm (I := I3) a ((X.term i).S.base.metric 0) y ≤ C

theorem terminalDerivativeBounds_iff_rmBallBoundAtZero_and_higherDerivativeBounds
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    TerminalDerivativeBounds X ↔
      TerminalRmBallBoundAtZero X ∧ TerminalHigherDerivativeBounds X := by
  constructor
  · intro h
    exact ⟨terminalRmBallBound_at_zero_of_terminalDerivativeBounds X h,
      fun rho hrho a _ => h rho hrho a⟩
  · rintro ⟨h0, hh⟩ rho hrho a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain ⟨C, hC, hb⟩ := h0 rho hrho
      refine ⟨Real.sqrt C, fun i y hy => ?_⟩
      have : PreconnectedSpace (X.term i).M := (X.connected i).toPreconnectedSpace
      have hy' : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0)
          (X.term i).basepoint y ≤ ENNReal.ofReal rho :=
        (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
          ((X.term i).S.base.metric 0) (X.term i).basepoint y) hrho.le).mpr
          (by simpa only [metricDistance] using hy)
      rw [curvDerivNorm]
      exact Real.sqrt_le_sqrt (hb i 0 ⟨le_rfl, le_rfl⟩ y hy')
    · exact hh rho hrho a (Nat.succ_le_of_lt ha)

theorem pointedFlowNotFlat_of_normalizedSequence {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) :
    PointedFlowNotFlat (X.term i) := by
  refine pointedFlowNotFlat_of_scalar_ne_zero (X.term i) (t := 0) ?_ (X.term i).basepoint ?_
  · rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  · rw [X.base_one i]
    norm_num

abbrev TerminalRmBallBoundAtSameTimeProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
      TerminalParabolicRmBallBoundAtSameTime X (-(modelDepth eps)) ρ

abbrev RicciTensorBoundProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ i : ℕ,
      ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
        0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
          (X.term i).S.ricciAt s x (vec2 v v) ≤
            ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
              ((X.term i).S.base.metric s).inner x v v

theorem terminalDerivativeBoundProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hK, hric⟩ := hric
  obtain ⟨e, he, hb⟩ :=
    bounded_curvature_at_distance_of_rmBallBoundAtSameTime_and_ricciTensorBound
      (kappa := kappa) (sigma := sigma) (Phi := Phi) hK hrm hric
  exact ⟨e, he, fun eps hp hle X => (hb eps hp hle X).2⟩

theorem terminalParabolicRmBallWindowProducer_of_rmBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hrm : TerminalRmBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    TerminalParabolicRmBallWindowProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hK, e₂, he₂, hric₂⟩ := hric
  obtain ⟨e₁, he₁, hrm₁⟩ := hrm
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X rho hrho => ?_⟩
  have hwin := normalizedSequence_modelDepth_window X hp
  have hric' : ∀ i : ℕ, ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
      ∀ v : TangentSpace I3 x,
        0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
          (X.term i).S.ricciAt s x (vec2 v v) ≤
            ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
              ((X.term i).S.base.metric s).inner x v v :=
    hric₂ eps hp (hle.trans (min_le_right e₁ e₂)) X
  obtain ⟨ρ, hρ, hnest⟩ :=
    terminalParabolicBallNesting_modelDepth_of_ricciTensorBound X hp hK hric' rho hrho
  refine ⟨ρ, hρ, ?_, hnest⟩
  exact terminalParabolicRmBallBound_of_rmBallBoundAtSameTime X (-(modelDepth eps)) (2 * ρ) K
    (by positivity) hK (fun i => (hwin i).1)
    (fun i s hs => (hwin i).2 ⟨hs.1.le, hs.2⟩) hric'
    (hrm₁ eps hp (hle.trans (min_le_left e₁ e₂)) X (2 * ρ) (by positivity))

abbrev TerminalScalarBallBoundAtSameTimeProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
      TerminalParabolicScalarBallBoundAtSameTime X (-(modelDepth eps)) ρ

theorem terminalDerivativeBoundProducer_of_scalarBallBoundAtSameTimeProducer_and_ricciTensorBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hscl : TerminalScalarBallBoundAtSameTimeProducer.{u} kappa sigma Phi)
    (hric : RicciTensorBoundProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨K, hK, hric⟩ := hric
  obtain ⟨e, he, hb⟩ :=
    bounded_curvature_at_distance_of_scalarBallBoundAtSameTime_and_ricciTensorBound
      (kappa := kappa) (sigma := sigma) (Phi := Phi) hPhi hK hscl hric
  exact ⟨e, he, fun eps hp hle X => (hb eps hp hle X).2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
