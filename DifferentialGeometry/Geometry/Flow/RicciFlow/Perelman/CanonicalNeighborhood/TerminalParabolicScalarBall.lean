import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicRmBallAtSameTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBoundedCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
  RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

def TerminalParabolicScalarBallBoundAtSameTime {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (start ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
    riemannianEDistOf (I := I3) ((X.term i).S.base.metric t) (X.term i).basepoint y ≤
      ENNReal.ofReal ρ →
    (X.term i).S.scalar t y ≤ C

theorem terminalParabolicScalarBallBoundAtSameTime_of_rmBallBoundAtSameTime
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (start ρ : ℝ) (h : TerminalParabolicRmBallBoundAtSameTime X start ρ) :
    TerminalParabolicScalarBallBoundAtSameTime X start ρ := by
  obtain ⟨C, hC, hb⟩ := h
  have hpos : 0 < (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    exact mul_pos (by rw [h3]; norm_num) (Real.sqrt_pos.mpr hC)
  refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C, hpos, ?_⟩
  intro i t ht y hy
  have hzero : curvCovDeriv (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric t) 0 =
      metricRm04 (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric t) := rfl
  have hrm : normSq0S (I := I3) ((X.term i).S.base.metric t) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric t) y) ≤ C := by
    have h0 := hb i t ht y hy
    rw [curvDerivNormSq, hzero, metricRm04_apply] at h0
    exact h0
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
    (I := I3) ((X.term i).S.base.metric t) y
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  rw [hdim] at hscal
  exact le_trans (le_abs_self _) (le_trans hscal
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))

private theorem exists_forall_lt_rescalePinchingFunction_le (Phi : ℝ → ℝ) (Q : ℕ → ℝ) (B : ℝ) :
    ∀ N : ℕ, ∃ tol : ℝ, ∀ i, i < N → rescalePinchingFunction (Q i) Phi B ≤ tol := by
  intro N
  induction N with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨tol, htol⟩ := ih
    refine ⟨max tol (rescalePinchingFunction (Q N) Phi B), fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact le_trans (htol i hlt) (le_max_left _ _)
    · subst heq
      exact le_max_right _ _

private theorem pinchingTolerance_of_tendsto {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {Q : ℕ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQtend : Filter.Tendsto Q Filter.atTop Filter.atTop) (B : ℝ) :
    ∃ tol : ℝ, 0 < tol ∧ ∀ i, ∀ u ∈ Set.Icc 0 B,
      rescalePinchingFunction (Q i) Phi u ≤ tol := by
  obtain ⟨Q₀, hQ₀, htail⟩ := exists_forall_rescalePinchingFunction_le hPhi one_pos (B := B)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hQtend.eventually (Filter.eventually_ge_atTop Q₀))
  obtain ⟨tol, htol⟩ := exists_forall_lt_rescalePinchingFunction_le Phi Q B N
  refine ⟨max tol 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun i u hu => ?_⟩
  by_cases hi : i < N
  · refine le_trans ?_ (le_max_left _ _)
    exact le_trans ((hPhi.rescale (hQ i)).mono hu.2) (htol i hi)
  · exact le_trans (htail (Q i) (hN i (le_of_not_gt hi)) u hu) (le_max_right _ _)

theorem terminalParabolicRmBallBoundAtSameTime_of_scalarBallBoundAtSameTime
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hPhi : AdmissiblePinchingFunction Phi) (start ρ : ℝ)
    (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier)
    (hscl : TerminalParabolicScalarBallBoundAtSameTime X start ρ) :
    TerminalParabolicRmBallBoundAtSameTime X start ρ := by
  obtain ⟨C, hC, hscl⟩ := hscl
  have hP : 0 < C / 4 := by linarith
  obtain ⟨tol, htolpos, htol⟩ := pinchingTolerance_of_tendsto hPhi (fun i => X.scale_pos i)
    X.scale_tendsto (4 * (C / 4))
  have hKpos : 0 < 2 * (2 * Real.sqrt 3) * (C / 4 + tol + tol) :=
    mul_pos (by positivity : (0 : ℝ) < 2 * (2 * Real.sqrt 3)) (by linarith)
  refine ⟨(2 * (2 * Real.sqrt 3) * (C / 4 + tol + tol)) ^ 2, pow_pos hKpos 2, ?_⟩
  intro i t ht y hy
  have hbridge : RmNormBoundOn (X.term i).S (2 * Real.sqrt 3) := fun t w basis horth a ha =>
    sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le (X.term i).S t w basis horth ha
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hub : (X.term i).S.scalar t y ≤ 4 * (C / 4) := by linarith [hscl i t ht y hy]
  have hrm := sqrt_rmNormSq_le_of_scalar_le (I := I3) (by positivity) hbridge
    (hPhi.rescale (X.scale_pos i)) (X.pinching i) hdim (hcarrier i ht) y hP hub
  have hA : rescalePinchingFunction (X.scale i) Phi (4 * (C / 4)) ≤ tol :=
    htol i (4 * (C / 4)) ⟨by linarith [hP], le_rfl⟩
  have hB : rescalePinchingFunction (X.scale i) Phi 0 ≤ tol :=
    htol i 0 ⟨le_rfl, by linarith [hP]⟩
  have hle : 2 * (2 * Real.sqrt 3) *
        (C / 4 + rescalePinchingFunction (X.scale i) Phi (4 * (C / 4)) +
          rescalePinchingFunction (X.scale i) Phi 0) ≤
      2 * (2 * Real.sqrt 3) * (C / 4 + tol + tol) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsq : FlowMetricBall.rmNormSq (X.term i).S t y ≤
      (2 * (2 * Real.sqrt 3) * (C / 4 + tol + tol)) ^ 2 :=
    (Real.sqrt_le_iff.mp (hrm.trans hle)).2
  have hcurv : FlowMetricBall.rmNormSq (X.term i).S t y =
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y := rfl
  rwa [hcurv] at hsq

theorem terminalParabolicRmBallBoundAtSameTime_iff_scalarBallBoundAtSameTime
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hPhi : AdmissiblePinchingFunction Phi) (start ρ : ℝ)
    (hcarrier : ∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier) :
    TerminalParabolicRmBallBoundAtSameTime X start ρ ↔
      TerminalParabolicScalarBallBoundAtSameTime X start ρ :=
  ⟨terminalParabolicScalarBallBoundAtSameTime_of_rmBallBoundAtSameTime X start ρ,
    terminalParabolicRmBallBoundAtSameTime_of_scalarBallBoundAtSameTime X hPhi start ρ hcarrier⟩

theorem bounded_curvature_at_distance_of_scalarBallBoundAtSameTime_and_ricciTensorBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {K : ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hK : 0 ≤ K)
    (hscl : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
        TerminalParabolicScalarBallBoundAtSameTime X (-(modelDepth eps)) ρ)
    (hric : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
          0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
            (X.term i).S.ricciAt s x (vec2 v v) ≤
              ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                ((X.term i).S.base.metric s).inner x v v) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X ∧ TerminalDerivativeBounds X := by
  obtain ⟨e, he, hscl⟩ := hscl
  refine bounded_curvature_at_distance_of_rmBallBoundAtSameTime_and_ricciTensorBound hK
    ⟨e, he, fun eps hp hle X ρ hρ =>
      terminalParabolicRmBallBoundAtSameTime_of_scalarBallBoundAtSameTime X hPhi
        (-(modelDepth eps)) ρ (fun i => (normalizedSequence_modelDepth_window X hp i).1)
        (hscl eps hp hle X ρ hρ)⟩ hric

theorem finite_horn_construction_of_scalarBallBoundAtSameTime_and_ricciTensorBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {K : ℝ} (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi) (hK : 0 ≤ K)
    (hscl : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
        TerminalParabolicScalarBallBoundAtSameTime X (-(modelDepth eps)) ρ)
    (hric : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
          0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
            (X.term i).S.ricciAt s x (vec2 v v) ≤
              ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                ((X.term i).S.base.metric s).inner x v v) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth := by
  obtain ⟨e, he, hscl⟩ := hscl
  exact finite_horn_construction_of_rmBallBoundAtSameTime_and_ricciTensorBound hkappa hsigma
    hPhi hK
    ⟨e, he, fun eps hp hle X ρ hρ =>
      terminalParabolicRmBallBoundAtSameTime_of_scalarBallBoundAtSameTime X hPhi
        (-(modelDepth eps)) ρ (fun i => (normalizedSequence_modelDepth_window X hp i).1)
        (hscl eps hp hle X ρ hρ)⟩ hric

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
