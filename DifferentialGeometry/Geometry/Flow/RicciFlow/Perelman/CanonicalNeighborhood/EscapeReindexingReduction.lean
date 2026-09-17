import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DistanceCurvatureEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBoundedCurvatureFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureHonest
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction

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

namespace NormalizedSequence

variable {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}

def reindex (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) : NormalizedSequence.{u} eps kappa sigma Phi where
  interval i := X.interval (k i)
  term i := X.term (k i)
  depth i := X.depth (k i)
  scale i := X.scale (k i)
  depth_pos i := X.depth_pos (k i)
  depth_buffer i := X.depth_buffer (k i)
  scale_pos i := X.scale_pos (k i)
  depth_tendsto := X.depth_tendsto.comp hk.tendsto_atTop
  scale_tendsto := X.scale_tendsto.comp hk.tendsto_atTop
  carrier_eq i := X.carrier_eq (k i)
  regular_eq i := X.regular_eq (k i)
  connected i := X.connected (k i)
  orientation i := X.orientation (k i)
  complete i t ht := X.complete (k i) t ht
  source_bound i := X.source_bound (k i)
  base_one i := X.base_one (k i)
  noncollapse i := X.noncollapse (k i)
  pinching i := X.pinching (k i)
  higher_good i t ht x h := X.higher_good (k i) t ht x h

@[simp] theorem reindex_term (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).term i = X.term (k i) := rfl

@[simp] theorem reindex_interval (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).interval i = X.interval (k i) := rfl

@[simp] theorem reindex_depth (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).depth i = X.depth (k i) := rfl

@[simp] theorem reindex_scale (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).scale i = X.scale (k i) := rfl

theorem reindex_id (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    X.reindex id strictMono_id = X := rfl

end NormalizedSequence

theorem curvatureBoundedWithin_reindex {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ) (hk : StrictMono k) {r : ℝ}
    (h : CurvatureBoundedWithin X r) : CurvatureBoundedWithin (X.reindex k hk) r := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun i y hy => hC (k i) y hy⟩

theorem exists_reindex_not_boundedAtDistance_of_subsequenceCurvatureEscape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : SubsequenceCurvatureEscape X) :
    ∃ k : ℕ → ℕ, ∃ hk : StrictMono k, ¬ BoundedAtDistance (X.reindex k hk) := by
  obtain ⟨radius, I, hradius, hI, _hinner, pts, hdist, hscal⟩ := h
  refine ⟨I, hI, fun hbdd => ?_⟩
  obtain ⟨C, hC⟩ := hbdd (radius + 1) (by linarith)
  have hd : ∀ᶠ i in Filter.atTop,
      metricDistance ((X.term (I i)).S.base.metric 0) (X.term (I i)).basepoint (pts i) <
        radius + 1 :=
    hdist.eventually (eventually_lt_nhds (by linarith))
  have hs : ∀ᶠ i in Filter.atTop, C < (X.term (I i)).S.scalar 0 (pts i) :=
    hscal.eventually_gt_atTop C
  obtain ⟨i, hdi, hsi⟩ := (hd.and hs).exists
  exact absurd (hC i (pts i) hdi.le) (not_le.mpr hsi)

theorem exists_reindex_nonempty_finiteControlledRadius_of_subsequenceCurvatureEscape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : SubsequenceCurvatureEscape X) :
    ∃ k : ℕ → ℕ, ∃ hk : StrictMono k, Nonempty (FiniteControlledRadius (X.reindex k hk)) := by
  obtain ⟨radius, I, hradius, hI, hinner, pts, hdist, hscal⟩ := h
  refine ⟨I, hI, ⟨⟨radius, hradius, ?_, pts, hdist, hscal⟩⟩⟩
  intro r hr hrlt
  exact curvatureBoundedWithin_reindex X I hI (hinner r hr hrlt)

def ConeLimitEscapeShell.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      SubsequenceCurvatureEscape X → Nonempty (ConeFlowLimit X.toFlowSequence)

theorem coneLimitEscapeShell_iff_noSubsequenceCurvatureEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    ConeLimitEscapeShell.{u} kappa sigma Phi ↔
      NoSubsequenceCurvatureEscapeShell.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, fun eps hp hle X hsub =>
      coneFlowLimit_not_nonempty (X := X.toFlowSequence) (h eps hp hle X hsub)⟩
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, fun eps hp hle X hsub => (h eps hp hle X hsub).elim⟩

theorem boundedAtDistanceShell_iff_coneLimitEscapeShell_of_smallScale
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r) :
    BoundedAtDistanceShell.{u} kappa sigma Phi ↔ ConeLimitEscapeShell.{u} kappa sigma Phi := by
  obtain ⟨e₁, r, he₁, hr, hs⟩ := hsmall
  constructor
  · rintro ⟨e₂, he₂, hb⟩
    refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X hsub => ?_⟩
    exact (boundedAtDistance_iff_subsequenceCurvatureEscape_coneFlowLimit X hr
      (hs eps hp (le_trans hle (min_le_left e₁ e₂)) X)).mp
      (hb eps hp (le_trans hle (min_le_right e₁ e₂)) X) hsub
  · rintro ⟨e₂, he₂, hc⟩
    refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps hp hle X => ?_⟩
    by_contra hf
    exact coneFlowLimit_not_nonempty (X := X.toFlowSequence)
      (hc eps hp (le_trans hle (min_le_right e₁ e₂)) X
        ((subsequenceCurvatureEscape_iff_not_boundedAtDistance_of_curvatureBoundedWithin X hr
          (hs eps hp (le_trans hle (min_le_left e₁ e₂)) X)).mpr hf))

theorem boundedAtDistanceShell_of_smallScale_of_coneLimitEscapeShell
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (h : ConeLimitEscapeShell.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  (boundedAtDistanceShell_iff_coneLimitEscapeShell_of_smallScale hsmall).mpr h

theorem boundedAtDistanceShell_of_smallScale_of_finiteHornRealization_of_coneLimitProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (hhorn : FiniteControlledRadiusFiniteHornRealization.{u} kappa sigma Phi)
    (hcone : FiniteHornConeLimitProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi := by
  obtain ⟨e₁, r, he₁, hr, hs⟩ := hsmall
  obtain ⟨e₂, he₂, h₂⟩ := hhorn
  obtain ⟨e₃, he₃, h₃⟩ := hcone
  refine ⟨min (min e₁ e₂) e₃, lt_min (lt_min he₁ he₂) he₃, fun eps hp hle X => ?_⟩
  have hle₁ : eps ≤ e₁ := le_trans hle (le_trans (min_le_left (min e₁ e₂) e₃) (min_le_left e₁ e₂))
  have hle₂ : eps ≤ e₂ := le_trans hle (le_trans (min_le_left (min e₁ e₂) e₃) (min_le_right e₁ e₂))
  have hle₃ : eps ≤ e₃ := le_trans hle (min_le_right (min e₁ e₂) e₃)
  by_contra hf
  obtain ⟨k, hk, hF⟩ := exists_reindex_nonempty_finiteControlledRadius_of_subsequenceCurvatureEscape
    (X := X) ((subsequenceCurvatureEscape_iff_not_boundedAtDistance_of_curvatureBoundedWithin X hr
      (hs eps hp hle₁ X)).mpr hf)
  obtain ⟨H⟩ := h₂ eps hp hle₂ (X.reindex k hk) hF
  exact coneFlowLimit_not_nonempty (X := (X.reindex k hk).toFlowSequence)
    (h₃ eps hp hle₃ (X.reindex k hk) ⟨H⟩)

theorem boundedAtDistanceShell_of_smallScale_of_escapeFiniteHornRealization_of_coneLimitProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (hhorn : EscapeFiniteHornRealization.{u} kappa sigma Phi)
    (hcone : FiniteHornConeLimitProducer.{u} kappa sigma Phi) :
    BoundedAtDistanceShell.{u} kappa sigma Phi :=
  boundedAtDistanceShell_of_smallScale_of_finiteHornRealization_of_coneLimitProducer hsmall
    (escapeFiniteHornRealization_iff_finiteControlledRadiusFiniteHornRealization.mp hhorn) hcone

theorem curvatureEscapeRealization_of_smallScale_of_finiteHornRealization_of_coneLimitProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsmall : ∃ epsStar r : ℝ, 0 < epsStar ∧ 0 < r ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, CurvatureBoundedWithin X r)
    (hhorn : FiniteControlledRadiusFiniteHornRealization.{u} kappa sigma Phi)
    (hcone : FiniteHornConeLimitProducer.{u} kappa sigma Phi) :
    CurvatureEscapeRealization.{u} kappa sigma Phi :=
  curvatureEscapeRealization_of_boundedAtDistance
    (boundedAtDistanceShell_of_smallScale_of_finiteHornRealization_of_coneLimitProducer
      hsmall hhorn hcone)

theorem finiteHornConeLimitProducer_iff_not_nonempty_realizedFiniteHorn
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    FiniteHornConeLimitProducer.{u} kappa sigma Phi ↔
      ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ¬ Nonempty (RealizedFiniteHorn X.toFlowSequence) := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, fun eps hp hle X hX =>
      coneFlowLimit_not_nonempty (X := X.toFlowSequence) (h eps hp hle X hX)⟩
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, fun eps hp hle X hX => absurd hX (h eps hp hle X)⟩

theorem exists_uniformly_locally_bounded_not_globally_bounded :
    ∃ f : ℕ → ℕ → ℝ, ∃ d : ℕ → ℕ → ℝ,
      (∀ rho : ℝ, 0 < rho → ∃ C : ℝ, ∀ i n, d i n ≤ rho → f i n ≤ C) ∧
        ¬ ∃ C : ℝ, ∀ i n, f i n ≤ C := by
  refine ⟨fun _ n => (n : ℝ), fun _ n => (n : ℝ), ?_, ?_⟩
  · intro rho _h
    exact ⟨rho, fun _ n hn => hn⟩
  · rintro ⟨C, hC⟩
    have h₁ : ((Nat.ceil (C + 1) : ℕ) : ℝ) ≤ C := hC 0 (Nat.ceil (C + 1))
    have h₂ : C + 1 ≤ ((Nat.ceil (C + 1) : ℕ) : ℝ) := Nat.le_ceil (C + 1)
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
