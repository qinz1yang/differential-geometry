import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedReindexing

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

structure FiniteControlledRadius {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) where
  radius : ℝ
  radius_pos : 0 < radius
  inner_bound : ∀ r : ℝ, 0 < r → r < radius → ∃ C : ℝ, ∀ i y,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r →
      (X.term i).S.scalar 0 y ≤ C
  points : ∀ i, (X.term i).M
  distance_limit : Filter.Tendsto (fun i => metricDistance
    ((X.term i).S.base.metric 0) (X.term i).basepoint (points i)) Filter.atTop (nhds radius)
  curvature_limit : Filter.Tendsto (fun i => (X.term i).S.scalar 0 (points i))
    Filter.atTop Filter.atTop

def CurvatureBoundedWithin {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (r : ℝ) : Prop :=
  ∃ C : ℝ, ∀ i : ℕ, ∀ y : (X.term i).M,
    metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r →
      (X.term i).S.scalar 0 y ≤ C

def DistanceCurvatureEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ radius : ℝ, 0 ≤ radius ∧
    (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
    (∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
        C < (X.term i).S.scalar 0 y)

def PositiveDistanceCurvatureEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧
    (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
    (∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
        C < (X.term i).S.scalar 0 y)

def RealizedDistanceCurvatureEscape {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧
    (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
    ∃ points : ∀ i : ℕ, (X.term i).M,
      Filter.Tendsto (fun i : ℕ => metricDistance ((X.term i).S.base.metric 0)
          (X.term i).basepoint (points i)) Filter.atTop (nhds radius) ∧
      Filter.Tendsto (fun i : ℕ => (X.term i).S.scalar 0 (points i))
        Filter.atTop Filter.atTop

private theorem exists_escape_radius_core {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : ¬ BoundedAtDistance X) :
    ∃ radius : ℝ,
      (∀ r : ℝ, 0 < r → r < radius → CurvatureBoundedWithin X r) ∧
      (∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
        metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
          C < (X.term i).S.scalar 0 y) := by
  classical
  simp only [BoundedAtDistance] at h
  push Not at h
  obtain ⟨rho, hrho, hfail⟩ := h
  have hfail' : ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho ∧
        C < (X.term i).S.scalar 0 y := by
    intro C
    obtain ⟨i, y, hd, hs⟩ := hfail C
    exact ⟨i, y, hd, hs⟩
  let S : Set ℝ := {r : ℝ | CurvatureBoundedWithin X r}
  have hS0 : (0 : ℝ) ∈ S := by
    refine ⟨0, fun i y hy => ?_⟩
    exact absurd hy (not_lt_of_ge ENNReal.toReal_nonneg)
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hSbdd : BddAbove S := by
    refine ⟨rho, fun r hr => le_of_not_gt fun hlt => ?_⟩
    obtain ⟨C, hC⟩ := hr
    obtain ⟨i, y, hd, hcs⟩ := hfail' C
    exact absurd (hC i y (lt_of_le_of_lt hd hlt)) (not_le.mpr hcs)
  refine ⟨sSup S, ?_, ?_⟩
  · intro r _ hlt
    obtain ⟨s, hs, hrs⟩ := (lt_csSup_iff hSbdd hSne).mp hlt
    obtain ⟨C, hC⟩ := hs
    exact ⟨C, fun i y hy => hC i y (lt_trans hy hrs)⟩
  · intro r hlt C
    by_contra hcon
    have hmem : r ∈ S := by
      refine ⟨C, fun i y hy => ?_⟩
      by_contra hgt
      exact hcon ⟨i, y, hy, lt_of_not_ge hgt⟩
    exact absurd (le_csSup hSbdd hmem) (not_le.mpr hlt)

private theorem nonneg_of_unbounded_beyond {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {radius : ℝ}
    (h : ∀ r : ℝ, radius < r → ∀ C : ℝ, ∃ i : ℕ, ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < r ∧
        C < (X.term i).S.scalar 0 y) : 0 ≤ radius := by
  by_contra hcon
  have hlt : radius < 0 := lt_of_not_ge hcon
  obtain ⟨i, y, hy, _⟩ := h (radius / 2) (by linarith) 0
  have h0 : radius / 2 ≤ metricDistance ((X.term i).S.base.metric 0)
      (X.term i).basepoint y :=
    le_trans (by linarith) ENNReal.toReal_nonneg
  exact absurd hy (not_lt_of_ge h0)

theorem curvatureBoundedWithin_mono {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {r r' : ℝ} (hr : r' ≤ r)
    (h : CurvatureBoundedWithin X r) : CurvatureBoundedWithin X r' := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun i y hy => hC i y (lt_of_lt_of_le hy hr)⟩

theorem boundedAtDistance_iff_forall_curvatureBoundedWithin {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    BoundedAtDistance X ↔ ∀ r : ℝ, 0 < r → CurvatureBoundedWithin X r := by
  constructor
  · intro h r hr
    obtain ⟨C, hC⟩ := h r hr
    exact ⟨C, fun i y hy => hC i y hy.le⟩
  · intro h rho hrho
    obtain ⟨C, hC⟩ := h (rho + 1) (by linarith)
    exact ⟨C, fun i y hy => hC i y (lt_of_le_of_lt hy (by linarith))⟩

theorem distanceCurvatureEscape_of_not_boundedAtDistance {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : ¬ BoundedAtDistance X) : DistanceCurvatureEscape X := by
  obtain ⟨radius, hinner, houter⟩ := exists_escape_radius_core X h
  exact ⟨radius, nonneg_of_unbounded_beyond houter, hinner, houter⟩

theorem positiveDistanceCurvatureEscape_of_curvatureBoundedWithin {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : ¬ BoundedAtDistance X) {r : ℝ} (hr : 0 < r) (hb : CurvatureBoundedWithin X r) :
    PositiveDistanceCurvatureEscape X := by
  obtain ⟨radius, hinner, houter⟩ := exists_escape_radius_core X h
  have hle : r ≤ radius := by
    by_contra hcon
    have hlt : radius < r := lt_of_not_ge hcon
    obtain ⟨C, hC⟩ := hb
    obtain ⟨i, y, hy, hcy⟩ := houter ((radius + r) / 2) (by linarith) C
    exact absurd (hC i y (lt_trans hy (by linarith))) (not_le.mpr hcy)
  exact ⟨radius, lt_of_lt_of_le hr hle, hinner, houter⟩

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

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
