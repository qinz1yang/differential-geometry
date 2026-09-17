import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersMinimalFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBoundedCurvatureFrontier

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
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
  RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

def EscapeFiniteHornRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      RealizedDistanceCurvatureEscape X → Nonempty (RealizedFiniteHorn X.toFlowSequence)

def FiniteControlledRadiusFiniteHornRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      Nonempty (FiniteControlledRadius X) → Nonempty (RealizedFiniteHorn X.toFlowSequence)

theorem escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    EscapeFiniteHornRealization.{u} kappa sigma Phi ↔
      FiniteControlledRadiusFiniteHornRealization.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps hp hle X hX =>
      hmain eps hp hle X (realizedDistanceCurvatureEscape_of_finiteControlledRadius hX.some)⟩
  · rintro ⟨e, he, hmain⟩
    exact ⟨e, he, fun eps hp hle X hX =>
      hmain eps hp hle X
        ((nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape X).mpr hX)⟩

theorem escapeFiniteHornRealization_of_finiteHornConstruction
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth) :
    EscapeFiniteHornRealization.{u} kappa sigma Phi := by
  obtain ⟨alphaMax, collarMin, haMax, haMax', hcMin, hmain⟩ := h
  obtain ⟨e, he, hstep⟩ :=
    hmain (alphaMax / 2) (half_pos haMax) (by linarith) (max collarMin 1) (le_max_left _ _)
  refine ⟨e, he, fun eps hp hle X hX => ?_⟩
  obtain ⟨H, _⟩ := hstep eps hp hle X
    ((nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape X).mpr hX).some
  exact ⟨H⟩

theorem finiteControlledRadiusFiniteHornRealization_of_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (h : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    FiniteControlledRadiusFiniteHornRealization.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  refine ⟨e, he, fun eps hp hle X hX => ?_⟩
  exact absurd hX (not_nonempty_finiteControlledRadius_of_boundedAtDistance X (hb eps hp hle X))

theorem nonempty_realizedFiniteHorn_of_curvatureEscapeRealization_of_escapeFiniteHornRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hesc : CurvatureEscapeRealization.{u} kappa sigma Phi)
    (hhorn : EscapeFiniteHornRealization.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ¬ BoundedAtDistance X → Nonempty (RealizedFiniteHorn X.toFlowSequence) := by
  obtain ⟨e₁, he₁, h₁⟩ := hesc
  obtain ⟨e₂, he₂, h₂⟩ := hhorn
  exact ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X hne =>
    h₂ eps hp (le_trans hle (min_le_right e₁ e₂)) X
      ((nonempty_finiteControlledRadius_iff_realizedDistanceCurvatureEscape X).mp
        (h₁ eps hp (le_trans hle (min_le_left e₁ e₂)) X hne))⟩

theorem boundedAtDistanceShell_of_escapeFiniteHornRealization_of_coneLimitProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hesc : CurvatureEscapeRealization.{u} kappa sigma Phi)
    (hhorn : EscapeFiniteHornRealization.{u} kappa sigma Phi)
    (hcone : FiniteHornConeLimitProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistance_of_curvatureEscapeRealization_of_finiteHornConstruction_of_coneLimitProducer
    hesc (escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization.mp hhorn)
    hcone

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
