import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StageContinuity_S85
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RicciNormDefect_S70

set_option autoImplicit false

/-!
# CH12-S85 / G1b: the Weak / Strong predicates of the first-failure bootstrap, closed step at regular times

`WeakAt_S85 K j0 J B η s` : at the time `s` every `x ∈ B` has a tracked position `z` in the active stage
`actS s` (survival of the transported ball), and at every tracked point `z` and every vector the LTF03
vector defect `|2 s Ric(V,V) + g_s(V,V)| ≤ η g_s(V,V)` holds (`g_s = stageMetric (actS s) s`).
`Strong` is `WeakAt` with `η / 2` (`weak_of_strong_S85` : `Strong ⇒ Weak`).

`weak_closed_regular_S85` : closed step at a time `s` with a constant active stage on `[s - ε, s]`
(regular time).  `weak_surv_event_S85` : the survival half of the closed step at an event time
(`tracked_survives_event_of_defect_S70`).  The defect half at an event time is left to the next lane.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

/-- Survival: the transported set `J '' B` has tracked positions in the active stage at time `s`. -/
def SurvAt_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) (s : ℝ) : Prop :=
  ∃ h : j0 ≤ actS_S70 K s, ∀ x ∈ B, ∃ z, TrackedAt_S70 K h J x z

/-- The vector defect `≤ η` at every tracked point of `B` at time `s` (in the active stage). -/
def DefectAllAt_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) (η s : ℝ) : Prop :=
  ∀ (h : j0 ≤ actS_S70 K s), ∀ x ∈ B, ∀ z, TrackedAt_S70 K h J x z →
    ∀ V : TangentSpace ThreeModel z, DefectAt_S85 K (actS_S70 K s) z V η s

/-- Weak (η) / Strong (η / 2) predicate of the first-failure bootstrap at time `s`. -/
def WeakAt_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) (η s : ℝ) : Prop :=
  SurvAt_S85 K j0 J B s ∧ DefectAllAt_S85 K j0 J B η s

theorem defectAt_mono_S85 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1))
    (z : (K.stage j).Carrier) (V : TangentSpace ThreeModel z) {η η' : ℝ} (r : ℝ) (h : η ≤ η')
    (hd : DefectAt_S85 K j z V η r) : DefectAt_S85 K j z V η' r := by
  unfold DefectAt_S85 at *
  have hnn : 0 ≤ (K.stageMetric j r).inner z V V := by
    rcases eq_or_ne V 0 with hV | hV
    · rw [hV]; simp
    · exact ((K.stageMetric j r).pos z V hV).le
  exact hd.trans (mul_le_mul_of_nonneg_right h hnn)

theorem weak_of_strong_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η : ℝ} (hη : 0 ≤ η) (s : ℝ)
    (h : WeakAt_S85 K j0 J B (η / 2) s) : WeakAt_S85 K j0 J B η s :=
  ⟨h.1, fun hle x hx z hz V =>
    defectAt_mono_S85 K _ z V s (by linarith) (h.2 hle x hx z hz V)⟩

theorem survAt_of_actS_eq_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {r s : ℝ} (hact : actS_S70 K r = actS_S70 K s)
    (h : SurvAt_S85 K j0 J B r) : SurvAt_S85 K j0 J B s := by
  unfold SurvAt_S85 at *
  generalize actS_S70 K s = j' at hact ⊢
  subst hact
  exact h

theorem defectAllAt_transport_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η r : ℝ} {j : Fin (K.eventCount + 1)}
    (hact : actS_S70 K r = j) (hr : DefectAllAt_S85 K j0 J B η r) :
    ∀ (h : j0 ≤ j), ∀ x ∈ B, ∀ z : (K.stage j).Carrier, TrackedAt_S70 K h J x z →
      ∀ V : TangentSpace ThreeModel z, DefectAt_S85 K j z V η r := by
  subst hact
  exact hr

/-- **Closed step at a regular time**: if the active stage is constant on `[s - ε, s]`, and `Weak` holds on
`[t, s)`, then `Weak` holds at `s`. -/
theorem weak_closed_regular_S85 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) (η : ℝ) {t s : ℝ} (ht0 : 0 ≤ t) (hts : t < s)
    (hs : s ≤ K.horizon) {ε : ℝ} (hε : 0 < ε)
    (hact : ∀ r ∈ Icc (s - ε) s, actS_S70 K r = actS_S70 K s)
    (hW : ∀ r ∈ Ico t s, WeakAt_S85 K j0 J B η r) : WeakAt_S85 K j0 J B η s := by
  set a := max t (s - ε) with ha
  have hta : t ≤ a := le_max_left _ _
  have hsa : s - ε ≤ a := le_max_right _ _
  have has : a < s := max_lt hts (by linarith)
  have hmem : ∀ r ∈ Icc a s, r ∈ Icc (s - ε) s := fun r hr => ⟨hsa.trans hr.1, hr.2⟩
  have hr0 : ∀ r ∈ Icc a s, r ∈ Icc (0 : ℝ) K.horizon := fun r hr =>
    ⟨ht0.trans (hta.trans hr.1), hr.2.trans hs⟩
  have hWa := hW a ⟨hta, has⟩
  refine ⟨survAt_of_actS_eq_S85 K j0 J B (hact a (hmem a ⟨le_rfl, has.le⟩)) hWa.1, ?_⟩
  intro h x hx z hz V
  refine defectAt_closed_S85 K (actS_S70 K s) z V η has (fun r hr => ?_) (fun r hr => ?_)
  · have h1 := actS_mem_stageDomain_S85 K (hr0 r hr)
    rwa [hact r (hmem r hr)] at h1
  · exact defectAllAt_transport_S85 K j0 J B (hact r (hmem r ⟨hr.1, hr.2.le⟩))
      (hW r ⟨hta.trans hr.1, hr.2⟩).2 h x hx z hz V

end GC.LongTime.Ch12
