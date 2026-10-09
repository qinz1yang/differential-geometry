import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem subsequenceCurvatureEscape_of_not_boundedAtDistance_of_modelScale
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → SubsequenceCurvatureEscape X := by
  obtain ⟨epsStar, r, heps, hr, hmain⟩ :=
    positiveDistanceCurvatureEscape_of_not_boundedAtDistance_of_modelScale hmod
  exact ⟨epsStar, r, heps, hr, fun eps hp hle sigma hsigma Phi hPhi X hf =>
    subsequenceCurvatureEscape_of_positiveDistanceCurvatureEscape X
      (hmain eps hp hle sigma hsigma Phi hPhi X hf)⟩

theorem boundedAtDistance_iff_subsequenceCurvatureEscape_coneFlowLimit
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {r : ℝ} (hr : 0 < r) (hb : CurvatureBoundedWithin X r) :
    BoundedAtDistance X ↔
      (SubsequenceCurvatureEscape X → Nonempty (ConeFlowLimit X.toFlowSequence)) := by
  constructor
  · intro hbdd hsub
    exact absurd hbdd (not_boundedAtDistance_of_subsequenceCurvatureEscape hsub)
  · intro h
    by_contra hf
    exact coneFlowLimit_not_nonempty (X := X.toFlowSequence)
      (h ((subsequenceCurvatureEscape_iff_not_boundedAtDistance_of_curvatureBoundedWithin
        X hr hb).mpr hf))

abbrev CurvatureEscapeRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      ¬ BoundedAtDistance X → Nonempty (FiniteControlledRadius X)

abbrev FiniteHornConeLimitProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      Nonempty (RealizedFiniteHorn X.toFlowSequence) →
        Nonempty (ConeFlowLimit X.toFlowSequence)

theorem boundedAtDistance_of_curvatureEscapeRealization_of_finiteHornConstruction_of_coneLimitProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hesc : CurvatureEscapeRealization.{u} kappa sigma Phi)
    (hconstruction : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        Nonempty (FiniteControlledRadius X) → Nonempty (RealizedFiniteHorn X.toFlowSequence))
    (hcone : FiniteHornConeLimitProducer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X := by
  obtain ⟨e₁, he₁, h₁⟩ := hesc
  obtain ⟨e₂, he₂, h₂⟩ := hconstruction
  obtain ⟨e₃, he₃, h₃⟩ := hcone
  refine ⟨min (min e₁ e₂) e₃, lt_min (lt_min he₁ he₂) he₃, fun eps hp hle X => ?_⟩
  have hle₁ : eps ≤ e₁ :=
    le_trans hle (le_trans (min_le_left (min e₁ e₂) e₃) (min_le_left e₁ e₂))
  have hle₂ : eps ≤ e₂ :=
    le_trans hle (le_trans (min_le_left (min e₁ e₂) e₃) (min_le_right e₁ e₂))
  have hle₃ : eps ≤ e₃ := le_trans hle (min_le_right (min e₁ e₂) e₃)
  by_contra hf
  obtain ⟨F⟩ := h₁ eps hp hle₁ X hf
  obtain ⟨H⟩ := h₂ eps hp hle₂ X ⟨F⟩
  exact coneFlowLimit_not_nonempty (X := X.toFlowSequence) (h₃ eps hp hle₃ X ⟨H⟩)

theorem curvatureEscapeRealization_of_boundedAtDistance
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X) :
    CurvatureEscapeRealization.{u} kappa sigma Phi := by
  obtain ⟨e, he, hb⟩ := h
  exact ⟨e, he, fun eps hp hle X hf => absurd (hb eps hp hle X) hf⟩


theorem FiniteControlledRadius.eventually_escape_window
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : FiniteControlledRadius X) {eta C : ℝ} (heta : 0 < eta) :
    ∀ᶠ i in Filter.atTop,
      |metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint (h.points i) - h.radius| < eta ∧
        C < (X.term i).S.scalar 0 (h.points i) := by
  have hdist : ∀ᶠ i in Filter.atTop,
      |metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint (h.points i) - h.radius| < eta := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp h.distance_limit) eta heta
  have hcurv : ∀ᶠ i in Filter.atTop,
      C < (X.term i).S.scalar 0 (h.points i) :=
    h.curvature_limit.eventually_gt_atTop C
  exact hdist.and hcurv

theorem FiniteControlledRadius.exists_source_index_after
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : FiniteControlledRadius X) {eta C : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      |metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint (h.points i) - h.radius| < eta ∧
        C < (X.term i).S.scalar 0 (h.points i) := by
  exact Filter.eventually_atTop.mp (h.eventually_escape_window heta)


theorem FiniteControlledRadius.exists_strictMono_source_escape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : FiniteControlledRadius X) :
    ∃ I : ℕ → ℕ, StrictMono I ∧ ∀ k : ℕ,
      |metricDistance ((X.term (I k)).S.base.metric 0) (X.term (I k)).basepoint (h.points (I k)) - h.radius| <
          1 / ((k : ℝ) + 1) ∧
        (k : ℝ) < (X.term (I k)).S.scalar 0 (h.points (I k)) := by
  let N : ℕ → ℕ := fun k => Classical.choose
    (h.exists_source_index_after (eta := 1 / ((k : ℝ) + 1)) (C := (k : ℝ)) (by positivity))
  have hN : ∀ k i, N k ≤ i →
      |metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint (h.points i) - h.radius| <
          1 / ((k : ℝ) + 1) ∧
        (k : ℝ) < (X.term i).S.scalar 0 (h.points i) := by
    intro k i hi
    exact Classical.choose_spec
      (h.exists_source_index_after (eta := 1 / ((k : ℝ) + 1)) (C := (k : ℝ)) (by positivity)) i hi
  let I : ℕ → ℕ := fun k => Nat.rec (N 0) (fun k prev => max (N (k + 1)) (prev + 1)) k
  have hstep : ∀ k, I k < I (k + 1) := by
    intro k
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (I k)) (Nat.le_max_right (N (k + 1)) (I k + 1))
  refine ⟨I, strictMono_nat_of_lt_succ hstep, ?_⟩
  intro k
  have hI : N k ≤ I k := by
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      exact le_max_left _ _
  exact hN k (I k) hI


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
