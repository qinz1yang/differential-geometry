import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakBootstrap_S93

set_option autoImplicit false

/-!
# CH12-S107 / G2c: `himprove` from its regular-time case (event times by the closed limit)

`himprove_of_regular_S107` : the `himprove` binder of `weak_bootstrap_S93` follows from
* `hreg` : the same statement at regular times `s` (`K.time (actS s) < s`) -- the LTF03 seed argument;
* `h0` : `WeakAt (η/2) t` (for `s = t`);
* `hevS` : the closed step at an event time `τ = time i.succ` for `Weak (η/2)` on `[t'', τ)`, any
  `t < t'' < τ` (= `weak_closed_event_S93` with `η/2`, per-event cutoff records from the F level).
At an event time `s > t`, every `r ∈ [t'', s)` with `t'' = (max t (time i.castSucc) + s)/2` is a regular time of
the stage `i.castSucc`, so `hreg` gives `Weak (η/2)` there and `hevS` closes at `s`.
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime

namespace GC.LongTime.Ch12

universe u v

theorem himprove_of_regular_S107 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η t : ℝ} (ht0 : 0 < t) (h2t : 2 * t ≤ K.horizon)
    (hj0t : j0 ≤ actS_S70 K t) (h0 : WeakAt_S85 K j0 J B (η / 2) t)
    (hreg : ∀ s ∈ Icc t (2 * t), K.time (actS_S70 K s) < s →
      (∀ r ∈ Icc t s, WeakAt_S85 K j0 J B η r) → WeakAt_S85 K j0 J B (η / 2) s)
    (hevS : ∀ i : Fin K.eventCount, j0 ≤ i.castSucc → ∀ t'' : ℝ, t < t'' → t'' < K.time i.succ →
      K.time i.succ ≤ 2 * t → (∀ r ∈ Ico t'' (K.time i.succ), WeakAt_S85 K j0 J B (η / 2) r) →
      WeakAt_S85 K j0 J B (η / 2) (K.time i.succ)) :
    ∀ s ∈ Icc t (2 * t), (∀ r ∈ Icc t s, WeakAt_S85 K j0 J B η r) →
      WeakAt_S85 K j0 J B (η / 2) s := by
  intro s hs hW
  have hs0 : s ∈ Icc (0 : ℝ) K.horizon := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht' : t ∈ Icc (0 : ℝ) K.horizon := ⟨ht0.le, by linarith⟩
  rcases hs.1.eq_or_lt with hst | hst
  · rw [← hst]; exact h0
  rcases (actS_time_le_S70 K hs0).eq_or_lt with hev | hregular
  · -- event time
    obtain ⟨i, hi⟩ := exists_succ_of_time_actS_S70 K (by linarith [hs.1]) hev
    have hsi : K.time i.succ = s := by rw [← hi]; exact hev
    have hj0i : j0 ≤ i.castSucc := by
      by_contra hnot
      have h1 : i.succ ≤ j0 := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hnot)
      have h2 := (K.time_strictMono.monotone (h1.trans hj0t)).trans (actS_time_le_S70 K ht')
      linarith [hs.1]
    have hlt : K.time i.castSucc < K.time i.succ := K.time_strictMono i.castSucc_lt_succ
    set a' := max t (K.time i.castSucc) with ha'
    have ha's : a' < s := by rw [← hsi]; exact max_lt (by linarith) hlt
    set t'' := (a' + s) / 2 with ht''
    have ht''a : a' < t'' := by rw [ht'']; linarith
    have ht''s : t'' < s := by rw [ht'']; linarith
    have htt'' : t < t'' := lt_of_le_of_lt (le_max_left _ _) ht''a
    refine hsi ▸ hevS i hj0i t'' htt'' (hsi ▸ ht''s) (hsi ▸ hs.2) (fun r hr => ?_)
    have hrs : r < s := by rw [← hsi]; exact hr.2
    have hrI : r ∈ Icc t (2 * t) := ⟨by linarith [hr.1], by linarith [hs.2]⟩
    have hact : actS_S70 K r = i.castSucc :=
      actS_eq_castSucc_S85 K i ⟨(le_max_right t _).trans (ht''a.le.trans hr.1), by rw [hsi]; exact hrs⟩
    refine hreg r hrI ?_ (fun r' hr' => hW r' ⟨hr'.1, hr'.2.trans hrs.le⟩)
    rw [hact]
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) ht''a) hr.1
  · exact hreg s hs hregular hW

end GC.LongTime.Ch12
