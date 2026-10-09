import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RicciSurvivor_S93
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedLift_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedRestrict_S70

set_option autoImplicit false

/-!
# CH12-S93 / G2a: the K-level bootstrap on `[t, 2t]` and the survivor lift from `Strong`

* `weak_bootstrap_S93` : `first_failure_bootstrap_S56` for `Strong := WeakAt (η/2)`, `Weak := WeakAt η` on
  `[t, 2t]`; the `hclosed` step is `weak_closed_regular_S85` at regular times and the inline binder `hev`
  at event times (discharged by `weak_closed_event_S93`); `hopen`, `himprove` are inline binders
  (frozen in DELIVERIES, `[FROZEN] CH12-S93`).
* `exists_lift_of_surv_S93` : survival at `s` gives a smooth lift `φ` on an open set with tracked values.
* `defect_clause_of_weak_S93` : `WeakAt` at `r` gives the vector-defect clause of the frozen hWA (v3)
  at the survivor image of `φ p`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

theorem weak_bootstrap_S93 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η t : ℝ} (hη : 0 ≤ η) (ht0 : 0 < t)
    (h2t : 2 * t ≤ K.horizon) (hj0t : j0 ≤ actS_S70 K t)
    (h0 : WeakAt_S85 K j0 J B (η / 2) t)
    (hev : ∀ i : Fin K.eventCount, t < K.time i.succ → K.time i.succ ≤ 2 * t →
      j0 ≤ i.castSucc → (∀ r ∈ Ico t (K.time i.succ), WeakAt_S85 K j0 J B η r) →
      WeakAt_S85 K j0 J B η (K.time i.succ))
    (hopen : ∀ s ∈ Ico t (2 * t), WeakAt_S85 K j0 J B (η / 2) s →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Icc s (s + ε), WeakAt_S85 K j0 J B η r)
    (himprove : ∀ s ∈ Icc t (2 * t), (∀ r ∈ Icc t s, WeakAt_S85 K j0 J B η r) →
      WeakAt_S85 K j0 J B (η / 2) s) :
    ∀ s ∈ Icc t (2 * t), WeakAt_S85 K j0 J B (η / 2) s := by
  refine first_failure_bootstrap_S56 (by linarith) (fun s => WeakAt_S85 K j0 J B (η / 2) s)
    (fun s => WeakAt_S85 K j0 J B η s) h0 (fun s hs => weak_of_strong_S85 K j0 J B hη s hs) ?_ hopen
    himprove
  intro s hs hW
  have hs0 : s ∈ Icc (0 : ℝ) K.horizon := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rcases actS_eq_left_or_event_S70 K hs0 with hev' | ⟨ε, hε, hact⟩
  · obtain ⟨i, hi⟩ := exists_succ_of_time_actS_S70 K (by linarith [hs.1]) hev'
    have hsi : K.time i.succ = s := by rw [← hi]; exact hev'
    have hj0i : j0 ≤ i.castSucc := by
      by_contra hnot
      have h1 : i.succ ≤ j0 := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hnot)
      have h2 := (K.time_strictMono.monotone (h1.trans hj0t)).trans
        (actS_time_le_S70 K (⟨ht0.le, by linarith⟩ : t ∈ Icc (0 : ℝ) K.horizon))
      linarith [hs.1]
    rw [← hsi] at hW ⊢
    exact hev i (by linarith [hs.1, hsi]) (by linarith [hs.2, hsi]) hj0i hW
  · exact weak_closed_regular_S85 K j0 J B η ht0.le hs.1 hs0.2 hε hact hW

theorem exists_lift_of_surv_S93 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 : Fin (K.eventCount + 1)) (J : H.Carrier → (K.stage j0).Carrier)
    (V : TopologicalSpace.Opens H.Carrier) (hJ : ContMDiffOn (𝓡 3) ThreeModel ∞ J V)
    (hnon : (V : Set H.Carrier).Nonempty) {s : ℝ} (hs : SurvAt_S85 K j0 J (V : Set H.Carrier) s) :
    ∃ h : j0 ≤ actS_S70 K s, ∃ φ : H.Carrier → K.backwardSurvivorDomain j0 (actS_S70 K s) h,
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧ ∀ p ∈ V,
        K.backwardSurvivorMap j0 (actS_S70 K s) h j0 le_rfl h (φ p) = J p ∧
        TrackedAt_S70 K h J p (φ p).val := by
  obtain ⟨h, hx⟩ := hs
  obtain ⟨φ, hφ, hφJ⟩ := exists_lift_on_open_S70 H K j0 (actS_S70 K s) h J V hJ hnon (fun p hp => by
    obtain ⟨z, x, -, hxJ⟩ := hx p hp
    exact ⟨x, hxJ⟩)
  exact ⟨h, φ, hφ, fun p hp => ⟨hφJ p hp, φ p, rfl, hφJ p hp⟩⟩

/-- The vector-defect clause of the frozen hWA (v3): at a time `r` with `WeakAt η r`, the survivor image
`q = backwardSurvivorMap j0 last h (actS r) _ _ (φ p)` of the lift `φ p` (restricted to the active stage of `r`)
satisfies `|2 r Ric(V,V) + g_r(V,V)| ≤ η g_r(V,V)`. -/
theorem defect_clause_of_weak_S93 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η r : ℝ} (hW : WeakAt_S85 K j0 J B η r)
    (last : Fin (K.eventCount + 1)) (hle : j0 ≤ last) (hr1 : j0 ≤ actS_S70 K r)
    (hr2 : actS_S70 K r ≤ last) (φ : X → K.backwardSurvivorDomain j0 last hle) (p : X) (hp : p ∈ B)
    (hφ : K.backwardSurvivorMap j0 last hle j0 le_rfl hle (φ p) = J p)
    (V : TangentSpace ThreeModel (K.backwardSurvivorMap j0 last hle (actS_S70 K r) hr1 hr2 (φ p))) :
    |2 * r * ricciTensor (K.stageMetric (actS_S70 K r) r)
        (K.backwardSurvivorMap j0 last hle (actS_S70 K r) hr1 hr2 (φ p)) V V +
      (K.stageMetric (actS_S70 K r) r).inner
        (K.backwardSurvivorMap j0 last hle (actS_S70 K r) hr1 hr2 (φ p)) V V| ≤
      η * (K.stageMetric (actS_S70 K r) r).inner
        (K.backwardSurvivorMap j0 last hle (actS_S70 K r) hr1 hr2 (φ p)) V V :=
  hW.2 hr1 p hp _ (tracked_restrict_S70 K hle hr1 hr2 J p (φ p) hφ) V

theorem actS_eq_activeStage_S93 (K : ObservedHistory.{u}) (r : Icc (0 : ℝ) K.horizon) :
    actS_S70 K r = K.activeStage r := by
  unfold actS_S70
  congr 1
  exact Subtype.ext (clampT_val_S70 K r.2)

/-- The window `[t, 2t]` of an observed history sits inside one stage range `[actS t, actS (2t)]`:
there are `a ≤ t < 2t < b ≤ horizon` with `actS t ≤ actS r ≤ actS (2t)` for all `r ∈ [a, b)` (the `stages`
datum of the frozen hWA with `first := actS t`, `last := actS (2t)`, `a := time (actS t)`). -/
theorem window_stages_S93 (K : ObservedHistory.{u}) {t : ℝ} (ht0 : 0 < t) (h2t : 2 * t < K.horizon) :
    ∃ a b : ℝ, a ≤ t ∧ 2 * t < b ∧ b ≤ K.horizon ∧ ∀ r ∈ Icc (0 : ℝ) K.horizon, r ∈ Ico a b →
      actS_S70 K t ≤ actS_S70 K r ∧ actS_S70 K r ≤ actS_S70 K (2 * t) := by
  have ht : t ∈ Icc (0 : ℝ) K.horizon := ⟨ht0.le, by linarith⟩
  have h2 : 2 * t ∈ Icc (0 : ℝ) K.horizon := ⟨by linarith, h2t.le⟩
  obtain ⟨ε, hε, hεh, hact⟩ := exists_actS_eq_right_S70 K h2 h2t
  refine ⟨K.time (actS_S70 K t), 2 * t + ε, actS_time_le_S70 K ht, by linarith, hεh, fun r hr hrab => ?_⟩
  refine ⟨le_actS_S70 K hr hrab.1, ?_⟩
  rcases le_or_gt r (2 * t) with h | h
  · exact actS_mono_S70 K hr h2 h
  · exact (hact r ⟨h.le, hrab.2.le⟩).le

/-- Survival at the start time: if `actS t = j0`, every point of `J '' B` is tracked at time `t` by itself
(the singleton trace); this is the survival half of `h0 : WeakAt (η/2) t`. -/
theorem survAt_start_S93 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {t : ℝ} (h : actS_S70 K t = j0) :
    SurvAt_S85 K j0 J B t :=
  survAt_of_stage_S85 K j0 J B h le_rfl (fun x _ =>
    ⟨J x, ⟨J x, K.mem_backwardSurvivorDomain_self j0 (J x)⟩, rfl,
      K.backwardSurvivorMap_last j0 j0 le_rfl ⟨J x, K.mem_backwardSurvivorDomain_self j0 (J x)⟩⟩)

end GC.LongTime.Ch12
