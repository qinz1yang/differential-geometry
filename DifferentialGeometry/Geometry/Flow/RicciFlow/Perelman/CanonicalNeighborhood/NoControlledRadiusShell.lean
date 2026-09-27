import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersMinimalFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBoundedCurvatureFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalShiDerivativeBounds

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

def NoPositiveDistanceCurvatureEscapeShell (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ PositiveDistanceCurvatureEscape X

theorem subsequenceCurvatureEscape_of_realizedDistanceCurvatureEscape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (h : RealizedDistanceCurvatureEscape X) :
    SubsequenceCurvatureEscape X := by
  obtain ⟨radius, hradius, hinner, points, hdist, hscal⟩ := h
  refine ⟨radius, id, hradius, strictMono_id, hinner, points, ?_, ?_⟩
  · simpa only [id_eq] using hdist
  · simpa only [id_eq] using hscal

theorem positiveDistanceCurvatureEscape_of_subsequenceCurvatureEscape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (h : SubsequenceCurvatureEscape X) :
    PositiveDistanceCurvatureEscape X := by
  obtain ⟨radius, subseq, hradius, _hmono, hinner, points, hdist, hscal⟩ := h
  refine ⟨radius, hradius, hinner, fun r hr C => ?_⟩
  have hclose : ∀ᶠ k : ℕ in Filter.atTop, metricDistance
      ((X.term (subseq k)).S.base.metric 0) (X.term (subseq k)).basepoint (points k) < r :=
    hdist.eventually (eventually_lt_nhds hr)
  have hlarge : ∀ᶠ k : ℕ in Filter.atTop,
      C < (X.term (subseq k)).S.scalar 0 (points k) := hscal.eventually_gt_atTop C
  obtain ⟨k, hk⟩ := (hclose.and hlarge).exists
  exact ⟨subseq k, points k, hk.1, hk.2⟩

theorem subsequenceCurvatureEscape_iff_positiveDistanceCurvatureEscape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    SubsequenceCurvatureEscape X ↔ PositiveDistanceCurvatureEscape X :=
  ⟨positiveDistanceCurvatureEscape_of_subsequenceCurvatureEscape,
    subsequenceCurvatureEscape_of_positiveDistanceCurvatureEscape X⟩

theorem positiveDistanceCurvatureEscape_of_finiteControlledRadius
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (h : FiniteControlledRadius X) :
    PositiveDistanceCurvatureEscape X :=
  positiveDistanceCurvatureEscape_of_subsequenceCurvatureEscape
    (subsequenceCurvatureEscape_of_finiteControlledRadius h)

theorem positiveDistanceCurvatureEscape_iff_distanceCurvatureEscape_and_boundedScale
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    PositiveDistanceCurvatureEscape X ↔
      DistanceCurvatureEscape X ∧ ∃ r : ℝ, 0 < r ∧ CurvatureBoundedWithin X r := by
  constructor
  · intro h
    obtain ⟨radius, hradius, hinner, houter⟩ := h
    exact ⟨distanceCurvatureEscape_of_positiveDistanceCurvatureEscape
        ⟨radius, hradius, hinner, houter⟩,
      radius / 2, half_pos hradius, hinner (radius / 2) (half_pos hradius) (by linarith)⟩
  · rintro ⟨h, r, hr, hb⟩
    obtain ⟨radius, _hnonneg, hinner, houter⟩ := h
    have hradius : 0 < radius := by
      by_contra hcon
      have hlt : radius < r := lt_of_le_of_lt (le_of_not_gt hcon) hr
      obtain ⟨C, hC⟩ := hb
      obtain ⟨i, y, hy, hcy⟩ := houter r hlt C
      exact absurd (hC i y hy) (not_le.mpr hcy)
    exact ⟨radius, hradius, hinner, houter⟩

theorem subsequenceCurvatureEscape_iff_not_boundedAtDistance_and_positive_boundedScale
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    SubsequenceCurvatureEscape X ↔
      ¬ BoundedAtDistance X ∧ ∃ r : ℝ, 0 < r ∧ CurvatureBoundedWithin X r := by
  constructor
  · intro h
    obtain ⟨radius, hradius, hinner, houter⟩ :=
      (subsequenceCurvatureEscape_iff_positiveDistanceCurvatureEscape X).mp h
    exact ⟨not_boundedAtDistance_of_distanceCurvatureEscape X
        (distanceCurvatureEscape_of_positiveDistanceCurvatureEscape
          ⟨radius, hradius, hinner, houter⟩),
      radius / 2, half_pos hradius, hinner (radius / 2) (half_pos hradius) (by linarith)⟩
  · rintro ⟨hnot, r, hr, hb⟩
    exact (subsequenceCurvatureEscape_iff_positiveDistanceCurvatureEscape X).mpr
      ((positiveDistanceCurvatureEscape_iff_distanceCurvatureEscape_and_boundedScale X).mpr
        ⟨distanceCurvatureEscape_of_not_boundedAtDistance X hnot, r, hr, hb⟩)

theorem noPositiveDistanceCurvatureEscapeShell_iff_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    NoPositiveDistanceCurvatureEscapeShell.{u} kappa sigma Phi ↔
      NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, fun eps hp hle X hs => h eps hp hle X
      ((subsequenceCurvatureEscape_iff_positiveDistanceCurvatureEscape X).mp hs)⟩
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, fun eps hp hle X hpd => h eps hp hle X
      ((subsequenceCurvatureEscape_iff_positiveDistanceCurvatureEscape X).mpr hpd)⟩

theorem noSubsequenceCurvatureEscapeShell_iff_forall_boundedAtDistance_or_noPositiveBoundedScale
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi ↔
      ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          BoundedAtDistance X ∨ ∀ r : ℝ, 0 < r → ¬ CurvatureBoundedWithin X r := by
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun eps hp hle X => ?_⟩
    by_cases hbdd : BoundedAtDistance X
    · exact Or.inl hbdd
    · refine Or.inr fun r hr hcbw => h eps hp hle X ?_
      exact (subsequenceCurvatureEscape_iff_not_boundedAtDistance_and_positive_boundedScale X).mpr
        ⟨hbdd, r, hr, hcbw⟩
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun eps hp hle X hs => ?_⟩
    obtain ⟨_hnot, r, hr, hcbw⟩ :=
      (subsequenceCurvatureEscape_iff_not_boundedAtDistance_and_positive_boundedScale X).mp hs
    rcases h eps hp hle X with hbdd | hnopos
    · exact not_boundedAtDistance_of_subsequenceCurvatureEscape hs hbdd
    · exact hnopos r hr hcbw

theorem noFiniteControlledRadius_of_noPositiveDistanceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : NoPositiveDistanceCurvatureEscapeShell.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ¬ Nonempty (FiniteControlledRadius X) := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X hfcr =>
    hb eps hp hle X (positiveDistanceCurvatureEscape_of_finiteControlledRadius hfcr.some)⟩

theorem noSubsequenceCurvatureEscapeShell_of_curvatureEscapeRealization_of_noFiniteControlledRadius
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hesc : CurvatureEscapeRealization.{u} kappa sigma Phi)
    (hnofcr : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ Nonempty (FiniteControlledRadius X)) :
    NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨e₁, he₁, h₁⟩ := hesc
  obtain ⟨e₂, he₂, h₂⟩ := hnofcr
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X hs =>
    h₂ eps hp (le_trans hle (min_le_right e₁ e₂)) X
      (h₁ eps hp (le_trans hle (min_le_left e₁ e₂)) X
        (not_boundedAtDistance_of_subsequenceCurvatureEscape hs))⟩

theorem noPositiveDistanceCurvatureEscapeShell_of_boundedAtDistanceShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} (h : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    NoPositiveDistanceCurvatureEscapeShell.{u} kappa sigma Phi :=
  noPositiveDistanceCurvatureEscapeShell_iff_noSubsequenceCurvatureEscapeShell.mpr
    (noSubsequenceCurvatureEscapeShell_of_boundedAtDistanceShell h)

private theorem scalar_at_zero_le_of_pointedFlowRmNormSqBounded
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (i : ℕ) {C : ℝ} (hC : PointedFlowRmNormSqBounded (X.term i) C) (y : (X.term i).M) :
    (X.term i).S.scalar 0 y ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max C 0) := by
  have h0 : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hrm : Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ max C 0 :=
    le_trans (hC 0 h0 y) (le_max_left _ _)
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm (I := I3)
    ((X.term i).S.base.metric 0) y
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  rw [hdim] at hscal
  exact le_trans (le_abs_self _) (le_trans hscal
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))

theorem boundedAtDistance_of_uniformRmNormSqBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : UniformRmNormSqBound X) : BoundedAtDistance X := by
  obtain ⟨K, hK⟩ := h
  refine fun rho _hrho =>
    ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max K 0), fun i y _hy =>
      scalar_at_zero_le_of_pointedFlowRmNormSqBounded X i (hK i) y⟩

theorem not_nonempty_finiteControlledRadius_of_uniformRmNormSqBound
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : UniformRmNormSqBound X) : ¬ Nonempty (FiniteControlledRadius X) :=
  not_nonempty_finiteControlledRadius_of_boundedAtDistance X
    (boundedAtDistance_of_uniformRmNormSqBound X h)

theorem boundedAtDistanceShell_of_uniformRmNormSqBoundProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformRmNormSqBoundProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X =>
    boundedAtDistance_of_uniformRmNormSqBound X (hb eps hp hle X)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
