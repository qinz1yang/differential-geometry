import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalFromJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

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
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

structure ParabolicCurvatureBoundsAtBase {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop where
  exists_window : ∀ rho : ℝ, 0 < rho → ∃ start curvature radius : ℝ,
    start < 0 ∧ 0 < curvature ∧ 0 < radius ∧
    (∀ i, Set.Icc start 0 ⊆ (X.interval i).carrier) ∧
    (∀ i, Set.Ico start 0 ⊆ (X.interval i).regular) ∧
    (∀ i, IsCompact {y : (X.term i).M |
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric start) (X.term i).basepoint y ≤
        ENNReal.ofReal (radius / Real.sqrt curvature)}) ∧
    (∀ i, ∀ t ∈ Set.Icc start 0, ∀ y : (X.term i).M,
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric start) (X.term i).basepoint y ≤
        ENNReal.ofReal (radius / Real.sqrt curvature) →
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ curvature ^ 2) ∧
    (∀ i, ∀ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho →
      riemannianEDistOf (I := I3) ((X.term i).S.base.metric start) (X.term i).basepoint y ≤
        ENNReal.ofReal (radius / (2 * Real.sqrt curvature)))

theorem boundedAtDistance_of_parabolicCurvatureBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : ParabolicCurvatureBoundsAtBase X) :
    BoundedAtDistance X := by
  intro rho hrho
  obtain ⟨start, curvature, radius, hstart, hK, hR, hcarrier, hregular, hball, hcurv, hcover⟩ :=
    h.exists_window rho hrho
  refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (curvature ^ 2), fun i y hy => ?_⟩
  have hzero : curvCovDeriv (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric 0) 0 =
      metricRm04 (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric 0) := rfl
  have hrm : Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ curvature ^ 2 := by
    have hpos : 0 < Real.sqrt curvature := Real.sqrt_pos.mpr hK
    have hle : radius / (2 * Real.sqrt curvature) ≤ radius / Real.sqrt curvature :=
      div_le_div_of_nonneg_left hR.le hpos (by linarith)
    have hcover' : riemannianEDistOf (I := I3) ((X.term i).S.base.metric start)
        (X.term i).basepoint y ≤ ENNReal.ofReal (radius / Real.sqrt curvature) :=
      (hcover i y hy).trans (ENNReal.ofReal_le_ofReal hle)
    have hz := hcurv i 0 ⟨hstart.le, le_rfl⟩ y hcover'
    rwa [curvDerivNormSq, hzero, metricRm04_apply] at hz
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  have hscalar := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
    (I := I3) (M := (X.term i).M) ((X.term i).S.base.metric 0) y
  rw [hdim] at hscalar
  calc metricScalarAt (I := I3) ((X.term i).S.base.metric 0) y
      ≤ |metricScalarAt (I := I3) ((X.term i).S.base.metric 0) y| := le_abs_self _
    _ ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
            (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y)) := hscalar
    _ ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (curvature ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)

theorem terminalDerivativeBounds_of_parabolicCurvatureBounds {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : ParabolicCurvatureBoundsAtBase X) :
    TerminalDerivativeBounds X := by
  intro rho hrho m
  obtain ⟨start, curvature, radius, hstart, hK, hR, hcarrier, hregular,
    hball, hcurv, hcover⟩ := h.exists_window rho hrho
  refine ⟨shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (curvature * (0 - start))
    radius * curvature / Real.sqrt (0 - start) ^ m, ?_⟩
  intro i y hy
  have hdim : 2 ≤ Module.finrank ℝ ThreeSpace := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    norm_num
  have ht : (0 : ℝ) ∈ Set.Ioc start 0 := ⟨hstart, le_rfl⟩
  exact KappaSolutions.shi_local_curvDerivNorm_terminal_of_solution_jets (X.term i).S
    (X.term i).isSolution hdim hstart hK hR (hcarrier i) (hregular i) (X.term i).basepoint
    (hball i) (hcurv i) m 0 ht y (hcover i y hy)

theorem bounded_curvature_at_distance_of_parabolicCurvatureBounds {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : ParabolicCurvatureBoundsAtBase X) :
    BoundedAtDistance X ∧ TerminalDerivativeBounds X :=
  ⟨boundedAtDistance_of_parabolicCurvatureBounds X h,
    terminalDerivativeBounds_of_parabolicCurvatureBounds X h⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
