import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakStrong_S85

set_option autoImplicit false

/-!
# CH12-S85 / G1c: survival half of the closed step at an event time

At an event time `τ = time i.succ` with `Weak η` on `[t, τ)`: all tracked points survive the event
(`tracked_survives_event_of_defect_S70` with the defect datum taken from `Weak`), giving `SurvAt τ`
and the survivor chart `E` (an isometry from the terminal metric of the incoming slab to the output
metric).  The defect at `τ` on the new stage (a left limit through `E`) is the remaining half.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

theorem actS_time_stage_S85 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1)) :
    actS_S70 K (K.time j) = j := by
  have h : clampT_S70 K (K.time j) = K.stageTime j :=
    Subtype.ext (clampT_val_S70 K ⟨K.time_nonneg j, K.time_le_horizon_at j⟩)
  unfold actS_S70
  rw [h]
  exact K.activeStage_stageTime j

theorem actS_eq_castSucc_S85 (K : ObservedHistory.{u}) (i : Fin K.eventCount) {r : ℝ}
    (hr : r ∈ Ico (K.time i.castSucc) (K.time i.succ)) : actS_S70 K r = i.castSucc := by
  have hr0 : r ∈ Icc (0 : ℝ) K.horizon :=
    ⟨(K.time_nonneg _).trans hr.1, hr.2.le.trans (K.time_le_horizon_at _)⟩
  refine le_antisymm ?_ (le_actS_S70 K hr0 hr.1)
  by_contra hnot
  have h1 : i.succ ≤ actS_S70 K r := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hnot)
  have h2 := (K.time_strictMono.monotone h1).trans (actS_time_le_S70 K hr0)
  exact absurd hr.2 (not_lt.mpr h2)

theorem survAt_stage_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {r : ℝ} {j : Fin (K.eventCount + 1)}
    (hact : actS_S70 K r = j) (hj : j0 ≤ j) (h : SurvAt_S85 K j0 J B r) :
    ∀ x ∈ B, ∃ z : (K.stage j).Carrier, TrackedAt_S70 K hj J x z := by
  unfold SurvAt_S85 at h
  subst hact
  exact h.2

theorem survAt_of_stage_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {r : ℝ} {j : Fin (K.eventCount + 1)}
    (hact : actS_S70 K r = j) (hj : j0 ≤ j)
    (h : ∀ x ∈ B, ∃ z : (K.stage j).Carrier, TrackedAt_S70 K hj J x z) : SurvAt_S85 K j0 J B r := by
  unfold SurvAt_S85
  subst hact
  exact ⟨hj, h⟩

/-- **Closed step at an event time (survival half).** -/
theorem weak_surv_event_S85 (K : ObservedHistory.{u}) {i : Fin K.eventCount} {pr : CutoffParameters}
    (R : GeometricCutoffRecord K i pr) {Λ η t : ℝ} (hΛ : 1 ≤ Λ) (hKΛ : 2 * (9 * 189) < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646) (hη : η ≤ 1) (ht0 : 0 < t) (hts : t < K.time i.succ)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ Real.sqrt (max t (K.time i.castSucc)))
    {j0 : Fin (K.eventCount + 1)} (hj0 : j0 ≤ i.castSucc) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) (hJo : IsOpen (J '' B))
    (hJp : IsPreconnected (J '' B)) (hBne : B.Nonempty)
    (hW : ∀ r ∈ Ico t (K.time i.succ), WeakAt_S85 K j0 J B η r) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (K.event i).incoming.terminalRegularOpen (K.stage i.succ).Carrier ∞,
      (∀ x ∈ B, ∀ z, TrackedAt_S70 K hj0 J x z →
        ∃ h : z ∈ (K.event i).incoming.terminalRegularRegion,
          (⟨z, h⟩ : (K.event i).incoming.terminalRegularOpen) ∈ E.source ∧
          TrackedAt_S70 K (hj0.trans i.castSucc_lt_succ.le) J x (E ⟨z, h⟩)) ∧
      (∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (K.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (K.event i).terminal.metric.inner z v w) ∧
      SurvAt_S85 K j0 J B (K.time i.succ) := by
  set a' := max t (K.time i.castSucc) with ha'
  have hlt : K.time i.castSucc < K.time i.succ := K.time_strictMono i.castSucc_lt_succ
  have ha'mem : a' ∈ Ico (K.time i.castSucc) (K.time i.succ) :=
    ⟨le_max_right _ _, max_lt hts hlt⟩
  have hta : t ≤ a' := le_max_left _ _
  have hact : ∀ r ∈ Ico a' (K.time i.succ), actS_S70 K r = i.castSucc := fun r hr =>
    actS_eq_castSucc_S85 K i ⟨(le_max_right _ _).trans hr.1, hr.2⟩
  have hsurv : ∀ x ∈ B, ∃ z : (K.stage i.castSucc).Carrier, TrackedAt_S70 K hj0 J x z :=
    survAt_stage_S85 K j0 J B (hact a' ⟨le_rfl, ha'mem.2⟩) hj0 (hW a' ⟨hta, ha'mem.2⟩).1
  obtain ⟨x₀, hx₀⟩ := hBne
  obtain ⟨z₀, hz₀⟩ := hsurv x₀ hx₀
  have hY := isPreconnected_tracked_S70 K hj0 J B hJp hsurv
  have hV := isOpen_tracked_S70 K hj0 J B hJo
  have hdef : ∀ z ∈ {z | ∃ x ∈ B, TrackedAt_S70 K hj0 J x z}, ∀ t' ∈ Ico a' (K.time i.succ),
      ∀ V : TangentSpace ThreeModel z,
        |2 * t' * ricciTensor ((K.event i).incoming.flow.base.metric t') z V V +
            ((K.event i).incoming.flow.base.metric t').inner z V V| ≤
          η * ((K.event i).incoming.flow.base.metric t').inner z V V := by
    rintro z ⟨x, hx, hz⟩ t' ht' V
    have h := defectAllAt_transport_S85 K j0 J B (hact t' ht') (hW t' ⟨hta.trans ht'.1, ht'.2⟩).2
      hj0 x hx z hz V
    simpa only [DefectAt_S85, ObservedHistory.stageMetric_castSucc_apply] using h
  obtain ⟨E, hE, hiso⟩ := tracked_survives_event_of_defect_S70 K R hΛ ha'mem (ht0.trans_le hta)
    hKΛ hδ hnom hj0 J B hY hV hη hdef hx₀ hz₀
  refine ⟨E, hE, hiso, ?_⟩
  refine survAt_of_stage_S85 K j0 J B (actS_time_stage_S85 K i.succ)
    (hj0.trans i.castSucc_lt_succ.le) (fun x hx => ?_)
  obtain ⟨z, hz⟩ := hsurv x hx
  obtain ⟨h, -, hz'⟩ := hE x hx z hz
  exact ⟨_, hz'⟩

end GC.LongTime.Ch12
