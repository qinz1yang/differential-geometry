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

def SubsequenceCurvatureEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ (radius : ℝ) (subseq : ℕ → ℕ),
    0 < radius ∧ StrictMono subseq ∧
    (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
    ∃ points : ∀ k : ℕ, (X.term (subseq k)).M,
      Filter.Tendsto (fun k : ℕ =>
          metricDistance ((X.term (subseq k)).S.base.metric 0)
            (X.term (subseq k)).basepoint (points k)) Filter.atTop (nhds radius) ∧
      Filter.Tendsto (fun k : ℕ => (X.term (subseq k)).S.scalar 0 (points k))
        Filter.atTop Filter.atTop

private theorem scalar_le_of_rmNormSqBounded {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ) {C : ℝ}
    (hC : PointedFlowRmNormSqBounded (X.term i) C) (y : (X.term i).M) :
    (X.term i).S.scalar 0 y ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max C 0) := by
  have h0 : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hrm : Tensor0SBundle.normSq0S (I := I3) ((X.term i).S.base.metric 0) y 4
      (metricRm04At (I := I3) ((X.term i).S.base.metric 0) y) ≤ max C 0 :=
    le_trans (hC 0 h0 y) (le_max_left _ _)
  have hscal := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
    (I := I3) ((X.term i).S.base.metric 0) y
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = Module.finrank ℝ ThreeSpace := rfl
  rw [hdim] at hscal
  exact le_trans (le_abs_self _) (le_trans hscal
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))

private theorem exists_scalar_le_prefix {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (N : ℕ) :
    ∃ C : ℝ, ∀ i : ℕ, i < N → ∀ y : (X.term i).M, (X.term i).S.scalar 0 y ≤ C := by
  induction N with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := X.source_bound N
    refine ⟨max C ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max C' 0)),
      fun i hi y => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact le_trans (hC i hlt y) (le_max_left _ _)
    · subst i
      exact le_trans (scalar_le_of_rmNormSqBounded X N hC' y) (le_max_right _ _)

private theorem abs_sub_lt_div_of_escapeRadii {R d : ℝ} {k : ℕ} (hR : 0 < R)
    (hlo : R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ d)
    (hhi : d < R * (((k : ℝ) + 2) / ((k : ℝ) + 1))) :
    |d - R| < R / ((k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hkey1 : R - R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) = R / ((k : ℝ) + 2) := by
    field_simp [hk2]
    ring
  have hkey2 : R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) - R = R / ((k : ℝ) + 1) := by
    field_simp
    ring
  have h1 : R - d ≤ R / ((k : ℝ) + 2) := by linarith
  have h2 : d - R < R / ((k : ℝ) + 1) := by linarith
  have h3 : R / ((k : ℝ) + 2) < R / ((k : ℝ) + 1) :=
    div_lt_div_of_pos_left hR (by positivity) (by linarith)
  rw [abs_lt]
  constructor <;> linarith

theorem subsequenceCurvatureEscape_of_positiveDistanceCurvatureEscape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : PositiveDistanceCurvatureEscape X) :
    SubsequenceCurvatureEscape X := by
  obtain ⟨R, hR, hinner, houter⟩ := h
  have hRin_pos : ∀ k : ℕ, 0 < R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) := by
    intro k
    have hk : 0 < ((k : ℝ) + 1) / ((k : ℝ) + 2) := by positivity
    positivity
  have hRin_lt : ∀ k : ℕ, R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) < R := by
    intro k
    have hk : ((k : ℝ) + 1) / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith
  have hRout_gt : ∀ k : ℕ, R < R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
    intro k
    have hk : 1 < ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    nlinarith
  have hbound : ∀ k : ℕ, ∃ C : ℝ, ∀ i : ℕ, ∀ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y <
        R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) →
      (X.term i).S.scalar 0 y ≤ C :=
    fun k => hinner _ (hRin_pos k) (hRin_lt k)
  let Cb : ℕ → ℝ := fun k => Classical.choose (hbound k)
  have hCb : ∀ (k : ℕ) (i : ℕ) (y : (X.term i).M),
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y <
        R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) →
      (X.term i).S.scalar 0 y ≤ Cb k :=
    fun k => Classical.choose_spec (hbound k)
  let T : ℕ → ℝ := fun k => max ((k : ℝ) + 1) (Cb k)
  have hgood : ∀ k N : ℕ, ∃ i : ℕ, N ≤ i ∧ ∃ y : (X.term i).M,
      R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤
          metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ∧
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y <
          R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) ∧
      (k : ℝ) < (X.term i).S.scalar 0 y := by
    intro k N
    by_contra hcon
    have hcon' : ∀ i : ℕ, N ≤ i → ∀ y : (X.term i).M,
        metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y <
          R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) →
        (X.term i).S.scalar 0 y ≤ T k := by
      intro i hi y hy
      by_cases hlo : R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤
          metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y
      · by_contra hge
        have hgt : (k : ℝ) < (X.term i).S.scalar 0 y := by
          have hk : (k : ℝ) ≤ T k :=
            le_trans (by linarith) (le_max_left ((k : ℝ) + 1) (Cb k))
          linarith [lt_of_not_ge hge]
        exact hcon ⟨i, hi, ⟨y, hlo, hy, hgt⟩⟩
      · have hlt : metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y <
            R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) := lt_of_not_ge hlo
        exact le_trans (hCb k i y hlt) (le_max_right ((k : ℝ) + 1) (Cb k))
    obtain ⟨B, hB⟩ := exists_scalar_le_prefix X N
    have hbdd : ∀ (i : ℕ) (y : (X.term i).M),
        metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y <
          R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) →
        (X.term i).S.scalar 0 y ≤ max B (T k) := by
      intro i y hy
      by_cases hi : i < N
      · exact le_trans (hB i hi y) (le_max_left B (T k))
      · exact le_trans (hcon' i (le_of_not_gt hi) y hy) (le_max_right B (T k))
    obtain ⟨i, y, hy, hcy⟩ :=
      houter (R * (((k : ℝ) + 2) / ((k : ℝ) + 1))) (hRout_gt k) (max B (T k))
    exact absurd (hbdd i y hy) (not_le.mpr hcy)
  let base : ℕ := Classical.choose (hgood 0 0)
  let step : ℕ → ℕ → ℕ := fun k prev => Classical.choose (hgood (k + 1) (prev + 1))
  let I : ℕ → ℕ := fun k => Nat.rec base step k
  have hI_lt : ∀ k : ℕ, I k < I (k + 1) := by
    intro k
    have h := (Classical.choose_spec (hgood (k + 1) (I k + 1))).1
    exact Nat.lt_of_succ_le h
  have hpoint : ∀ k : ℕ, ∃ y : (X.term (I k)).M,
      R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤
          metricDistance ((X.term (I k)).S.base.metric 0) (X.term (I k)).basepoint y ∧
      metricDistance ((X.term (I k)).S.base.metric 0) (X.term (I k)).basepoint y <
          R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) ∧
      (k : ℝ) < (X.term (I k)).S.scalar 0 y := by
    intro k
    cases k with
    | zero => exact (Classical.choose_spec (hgood 0 0)).2
    | succ k => exact (Classical.choose_spec (hgood (k + 1) (I k + 1))).2
  let pts : ∀ k : ℕ, (X.term (I k)).M := fun k => Classical.choose (hpoint k)
  have hpts : ∀ k : ℕ,
      R * (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤
          metricDistance ((X.term (I k)).S.base.metric 0) (X.term (I k)).basepoint (pts k) ∧
      metricDistance ((X.term (I k)).S.base.metric 0) (X.term (I k)).basepoint (pts k) <
          R * (((k : ℝ) + 2) / ((k : ℝ) + 1)) ∧
      (k : ℝ) < (X.term (I k)).S.scalar 0 (pts k) :=
    fun k => Classical.choose_spec (hpoint k)
  have hpts_abs : ∀ k : ℕ,
      |metricDistance ((X.term (I k)).S.base.metric 0) (X.term (I k)).basepoint (pts k) - R| <
        R / ((k : ℝ) + 1) :=
    fun k => abs_sub_lt_div_of_escapeRadii hR (hpts k).1 (hpts k).2.1
  have hlim : Filter.Tendsto (fun k : ℕ => R / ((k : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv, one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R
  have habs : Filter.Tendsto (fun k : ℕ =>
      |metricDistance ((X.term (I k)).S.base.metric 0) (X.term (I k)).basepoint (pts k) - R|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun k => abs_nonneg _) (fun k => (hpts_abs k).le) hlim
  refine ⟨R, I, hR, strictMono_nat_of_lt_succ hI_lt, hinner, pts, ?_, ?_⟩
  · refine Metric.tendsto_nhds.mpr (fun eps heps => ?_)
    filter_upwards [habs.eventually (eventually_lt_nhds heps)] with k hk
    rwa [Real.dist_eq]
  · refine Filter.tendsto_atTop_atTop.mpr (fun b => ⟨Nat.ceil b, fun k hk => ?_⟩)
    exact le_trans (Nat.le_ceil b) (le_trans (by exact_mod_cast hk) (le_of_lt (hpts k).2.2))

theorem not_boundedAtDistance_of_subsequenceCurvatureEscape
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (h : SubsequenceCurvatureEscape X) : ¬ BoundedAtDistance X := by
  obtain ⟨R, sub, hR, _hmono, _hinner, pts, hdist, hscal⟩ := h
  intro hb
  obtain ⟨C, hC⟩ := hb (R + 1) (by linarith)
  have hd : ∀ᶠ k in Filter.atTop,
      metricDistance ((X.term (sub k)).S.base.metric 0) (X.term (sub k)).basepoint (pts k) <
        R + 1 :=
    hdist.eventually (eventually_lt_nhds (by linarith))
  have hs : ∀ᶠ k in Filter.atTop, C < (X.term (sub k)).S.scalar 0 (pts k) :=
    hscal.eventually (Filter.eventually_gt_atTop C)
  obtain ⟨k, hdk, hsk⟩ := (hd.and hs).exists
  exact absurd (hC (sub k) (pts k) hdk.le) (not_le.mpr hsk)

theorem subsequenceCurvatureEscape_iff_not_boundedAtDistance_of_curvatureBoundedWithin
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {r : ℝ} (hr : 0 < r) (hb : CurvatureBoundedWithin X r) :
    SubsequenceCurvatureEscape X ↔ ¬ BoundedAtDistance X :=
  ⟨not_boundedAtDistance_of_subsequenceCurvatureEscape,
    fun h => subsequenceCurvatureEscape_of_positiveDistanceCurvatureEscape X
      (positiveDistanceCurvatureEscape_of_curvatureBoundedWithin X h hr hb)⟩

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
