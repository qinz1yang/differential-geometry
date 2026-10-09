import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCutScaleProtection

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- The radius multiplier can dominate both the seed multiplier and the
curvature threshold, uniformly in the event and its neck index. -/
theorem exists_cutoff_multiplier_CX2 (K Λ₀ : ℝ) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ Λ₀ ≤ Λ ∧ 2 * K < Λ ^ 2 := by
  let Λ := max 1 (max Λ₀ (2 * K + 1))
  have h₁ : 1 ≤ Λ := le_max_left _ _
  have h₂ : Λ₀ ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : 2 * K + 1 ≤ Λ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Λ, h₁, h₂, ?_⟩
  nlinarith

/-- Convert the recent nominal-radius hypothesis to the actual cut-neck
threshold in `EventCutScaleProtection`; the factor 4323 is retained exactly. -/
theorem cutoff_threshold_of_nominal_CX2 {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    {r Λ K : ℝ} (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * K < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ r) :
    ∀ j, K / r ^ 2 < (1 - 4323 * R.delta j) * (R.neck j).scale := by
  intro j
  have hn : 0 < R.nominalRadius ⟨j⟩ := R.nominal_pos _
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hn2 : 0 < (R.nominalRadius ⟨j⟩) ^ 2 := sq_pos_of_pos hn
  have hsquare := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ Λ) hn.le) (hnom ⟨j⟩) 2
  rw [mul_pow] at hsquare
  have hprod : 2 * K * (R.nominalRadius ⟨j⟩) ^ 2 < r ^ 2 :=
    (mul_lt_mul_of_pos_right hKΛ hn2).trans_le hsquare
  rw [R.scale_eq]
  calc
    K / r ^ 2 < 1 / (2 * (R.nominalRadius ⟨j⟩) ^ 2) := by
      apply (div_lt_div_iff₀ hr2 (by positivity)).mpr
      nlinarith
    _ = (1 / 2 : ℝ) * ((R.nominalRadius ⟨j⟩) ^ 2)⁻¹ := by
      rw [one_div, mul_inv_rev]
      ring
    _ ≤ (1 - 4323 * R.delta j) * ((R.nominalRadius ⟨j⟩) ^ 2)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hn2.le)
      linarith [hδ j]

/-- A connected low-curvature terminal set containing a known seed crossing
survives the event, with the genuine metric-preserving partial diffeomorphism. -/
theorem survivor_chart_of_nominal_threshold_CX2
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {r Λ K : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * K < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    {U : Set (H.event i).incoming.terminalRegularOpen} (hU : IsPreconnected U)
    (hscalar : ∀ x ∈ U, metricScalarAt (H.event i).terminal.metric x ≤ K / r ^ 2)
    {x : (H.event i).incoming.terminalRegularOpen} (hx : x ∈ U)
    {y : (H.stage i.succ).Carrier} (hcross : (H.event i).RegularCrossing x.val y) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      U ⊆ E.source ∧ E x = y ∧
      (∀ z ∈ E.source, (H.event i).RegularCrossing z.val (E z)) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (H.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (H.event i).terminal.metric.inner z v w := by
  exact R.exists_survivor_partialDiffeomorph_of_scalar_upper_bound R.old_eq_retained
    (fun j => (hδ j).trans (by norm_num))
    (cutoff_threshold_of_nominal_CX2 R hr hΛ hKΛ hδ hnom) hU hscalar hx hcross

/-- Decay of the original accuracy controls every actual record in a late
half-time window, without a history-dependent cutoff time. -/
theorem eventually_recent_cutoff_accuracy_CX2
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
      ∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ j, (Hp.records n i).delta j ≤ 1 / 8646 := by
  obtain ⟨B, hB⟩ := hdec (1 / 8646) (by norm_num)
  refine ⟨max 1 (2 * (B + 1)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht n i hi j
  have htime : B < (F.tower.history n).time i.succ := by
    have hT := le_max_right 1 (2 * (B + 1))
    linarith [hi.1]
  have hd := (Hp.records n i).delta_le j
  rw [Hp.accuracy_eq] at hd
  exact hd.trans (hB _ htime).le

end GC.LongTime.Ch12
