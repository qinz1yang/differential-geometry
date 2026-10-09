import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84TraceScalar_S74

/-!
# CH12-S138, group 1a: the backward trace with the scalar barrier, crossing supplied by the partial trace

The same construction as `exists_trace_scalar_bound_S74`, but the existence of a regular crossing at an event is an
abstract hypothesis `hcross` that may look at the *partial trace* `A` through the point (this is what the `hnc`
clause of `hcore` needs: it is a statement about traces):

* `event_step_nc_S138`: `event_step_S74` with the cap exclusion replaced by `hcross : ∃ p', RegularCrossing p' q`;
* `exists_backwardTrace_of_step_tr_S138`: `exists_backwardTrace_of_step_S74` where `hstep` also gets the partial trace;
* `exists_trace_scalar_bound_nc_S138`: `exists_trace_scalar_bound_S74`, with `hcross`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace GC.LongTime.Ch12

universe u

theorem event_step_nc_S138 {H : ObservedHistory.{u}} (i : Fin H.eventCount)
    {M β C u a0 : ℝ} (hC : 0 < C) (hβ : 0 < β) (hβM : β * M < 1)
    {θ : ℝ → ℝ} (hθ : ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ), θ t ≤ M)
    (hP2 : ∀ y : (H.stage i.castSucc).Carrier, ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      θ t < (H.event i).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t y ^ 2)
    (hu : H.time i.succ ≤ u) (ha0 : a0 < H.time i.succ) (hden : 0 < β - 2 * C * (u - a0))
    (q : (H.stage i.succ).Carrier)
    (hq : metricScalarAt (H.initialMetric i.succ) q ≤ (β - 2 * C * (u - H.time i.succ))⁻¹)
    (hcross : ∃ p' : (H.stage i.castSucc).Carrier, (H.event i).RegularCrossing p' q) :
    ∃ p' : (H.stage i.castSucc).Carrier, (H.event i).RegularCrossing p' q ∧
      ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ), a0 ≤ t →
        metricScalarAt (H.stageMetric i.castSucc t) p' ≤ (β - 2 * C * (u - t))⁻¹ := by
  have hlt : H.time i.castSucc < H.time i.succ := H.time_strictMono (Fin.castSucc_lt_succ (i := i))
  have hout : metricScalarAt (H.event i).outputMetric q ≤ (β - 2 * C * (u - H.time i.succ))⁻¹ := by
    rw [H.event_output i]; exact hq
  obtain ⟨p', hp'⟩ := hcross
  refine ⟨p', hp', fun t ht hat => ?_⟩
  have hL := flow_scalar_tendsto_of_regularCrossing_S74 (H.event i) hp'
  have hc1 : H.time i.castSucc ≤ max a0 (H.time i.castSucc) := le_max_right _ _
  have hc2 : max a0 (H.time i.castSucc) < H.time i.succ := max_lt ha0 hlt
  have hbar := incoming_scalar_backward_barrier_Ico_S74 (H.event i).incoming p' hC (θ := θ)
    (hP2 p') (c := max a0 (H.time i.castSucc)) hc1 hc2 hβ hβM (σ0 := u - H.time i.succ)
    (by linarith) hθ
    (by
      have h1 : u - H.time i.succ + (H.time i.succ - max a0 (H.time i.castSucc)) =
          u - max a0 (H.time i.castSucc) := by ring
      rw [h1]
      have : 2 * C * (u - max a0 (H.time i.castSucc)) ≤ 2 * C * (u - a0) :=
        mul_le_mul_of_nonneg_left (by linarith [le_max_left a0 (H.time i.castSucc)]) (by positivity)
      linarith)
    hL hout t ⟨max_le hat ht.1, ht.2⟩
  have heq : u - H.time i.succ + (H.time i.succ - t) = u - t := by ring
  rw [heq] at hbar
  have hs : metricScalarAt (H.stageMetric i.castSucc t) p' =
      (H.event i).incoming.flow.scalar t p' := by
    simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    rfl
  rw [hs]
  exact hbar

theorem exists_backwardTrace_of_step_tr_S138 (H : ObservedHistory.{u})
    (Good : ∀ j : Fin (H.eventCount + 1), (H.stage j).Carrier → Prop)
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {y : (H.stage last).Carrier}
    (hy : Good last y)
    (hstep : ∀ i : Fin H.eventCount, first ≤ i.castSucc → ∀ hs : i.succ ≤ last,
      ∀ A : BackwardPointTrace H i.succ last hs y, Good i.succ (A.point i.succ le_rfl hs) →
        ∃ p : (H.stage i.castSucc).Carrier,
          (H.event i).RegularCrossing p (A.point i.succ le_rfl hs) ∧ Good i.castSucc p) :
    ∃ X : BackwardPointTrace H first last hle y,
      ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last), Good j (X.point j hf hl) := by
  have key : ∀ m : Fin (H.eventCount + 1), first ≤ m → ∀ hml : m ≤ last,
      ∃ A : BackwardPointTrace H m last hml y,
        ∀ (j : Fin (H.eventCount + 1)) (hf : m ≤ j) (hl : j ≤ last), Good j (A.point j hf hl) := by
    intro m
    induction m using Fin.reverseInduction with
    | last =>
      intro _ hml
      have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hml
      subst last
      refine ⟨BackwardPointTrace.singleton H _ y, fun j hf hl => ?_⟩
      obtain rfl : j = Fin.last H.eventCount := le_antisymm hl hf
      exact (BackwardPointTrace.singleton H _ y).endpoint_eq ▸ hy
    | cast i ih =>
      intro hfi hml
      by_cases he : i.castSucc = last
      · subst last
        refine ⟨BackwardPointTrace.singleton H _ y, fun j hf hl => ?_⟩
        obtain rfl : j = i.castSucc := le_antisymm hl hf
        exact (BackwardPointTrace.singleton H _ y).endpoint_eq ▸ hy
      · have hs : i.succ ≤ last := by
          apply Fin.le_iff_val_le_val.mpr
          have hlt : i.castSucc < last := lt_of_le_of_ne hml he
          exact Nat.succ_le_iff.mpr hlt
        obtain ⟨A, hA⟩ := ih (hfi.trans (Fin.castSucc_lt_succ (i := i)).le) hs
        obtain ⟨p, hcross, hp⟩ := hstep i hfi hs A (hA i.succ le_rfl hs)
        refine ⟨A.prepend p hcross, fun j hf hl => ?_⟩
        by_cases hji : j = i.castSucc
        · subst hji
          rw [BackwardPointTrace.prepend_point_first]
          exact hp
        · have hsucc : i.succ ≤ j := by
            apply Fin.le_iff_val_le_val.mpr
            have hlt : i.castSucc < j := lt_of_le_of_ne hf (Ne.symm hji)
            exact Nat.succ_le_iff.mpr hlt
          have hh : (A.prepend p hcross).point j hf hl = A.point j hsucc hl := by
            simp [BackwardPointTrace.prepend, hji]
          rw [hh]
          exact hA j hsucc hl
  exact key first le_rfl hle

theorem exists_trace_scalar_bound_nc_S138 (H : ObservedHistory.{u})
    {C M β : ℝ} {θ : ℝ → ℝ} (hC : 0 < C) (hβ : 0 < β) (hβM : β * M < 1)
    (hP2e : ∀ (i : Fin H.eventCount) (y : (H.stage i.castSucc).Carrier),
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      θ t < (H.event i).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t y ^ 2)
    (hP2f : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier),
      ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon,
      θ t < (H.finalSlab h).flow.scalar t y →
      |derivWithin (fun v => (H.finalSlab h).flow.scalar v y) (Iic t) t| ≤
        C * (H.finalSlab h).flow.scalar t y ^ 2)
    {a u : Icc (0 : ℝ) H.horizon} (hau : a ≤ u) (hθ : ∀ t, t ≤ (u : ℝ) → θ t ≤ M)
    (hreg : H.time (H.activeStage u) < (u : ℝ))
    (hden : 0 < β - 2 * C * ((u : ℝ) - a))
    (x0 : (H.stage (H.activeStage u)).Carrier)
    (hx0 : metricScalarAt (H.stageMetric (H.activeStage u) u) x0 < β⁻¹)
    (hcross : ∀ i : Fin H.eventCount, H.activeStage a ≤ i.castSucc → ∀ hl : i.succ ≤ H.activeStage u,
      ∀ A : BackwardPointTrace H i.succ (H.activeStage u) hl x0,
      metricScalarAt (H.event i).outputMetric (A.point i.succ le_rfl hl) ≤
        (β - 2 * C * ((u : ℝ) - a))⁻¹ →
      ∃ p' : (H.stage i.castSucc).Carrier, (H.event i).RegularCrossing p' (A.point i.succ le_rfl hl)) :
    ∃ X : BackwardPointTrace H (H.activeStage a) (H.activeStage u) (H.activeStage_mono hau) x0,
      ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwu : w ≤ u),
        metricScalarAt (H.stageMetric (H.activeStage w) w)
          (X.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwu)) ≤
          (β - 2 * C * ((u : ℝ) - w))⁻¹ := by
  let Good : ∀ j : Fin (H.eventCount + 1), (H.stage j).Carrier → Prop := fun j q =>
    ∀ t ∈ H.stageDomain j, (a : ℝ) ≤ t → t ≤ (u : ℝ) →
      metricScalarAt (H.stageMetric j t) q ≤ (β - 2 * C * ((u : ℝ) - t))⁻¹
  have hy : Good (H.activeStage u) x0 :=
    top_stage_barrier_S74 H hC hβ hβM hP2e hP2f u (fun t _ ht => hθ t ht) hreg hau hden x0 hx0
  have hstep : ∀ i : Fin H.eventCount, H.activeStage a ≤ i.castSucc → ∀ hl : i.succ ≤ H.activeStage u,
      ∀ A : BackwardPointTrace H i.succ (H.activeStage u) hl x0,
      Good i.succ (A.point i.succ le_rfl hl) →
        ∃ p' : (H.stage i.castSucc).Carrier,
          (H.event i).RegularCrossing p' (A.point i.succ le_rfl hl) ∧ Good i.castSucc p' := by
    intro i hf hl A hq
    have hlast : H.time i.succ ≤ (u : ℝ) :=
      (H.time_strictMono.monotone hl).trans (H.activeStage_time_le u)
    have hlt : (a : ℝ) < H.time i.succ := by
      by_contra hn
      rw [not_lt] at hn
      have h1 : i.succ ≤ H.activeStage a := H.le_activeStage a _ hn
      exact absurd (hf.trans_lt (Fin.castSucc_lt_succ (i := i))) (not_lt.mpr h1)
    have hq0 : metricScalarAt (H.initialMetric i.succ) (A.point i.succ le_rfl hl) ≤
        (β - 2 * C * ((u : ℝ) - H.time i.succ))⁻¹ := by
      have := hq (H.time i.succ) (time_mem_stageDomain_S74 H i.succ) hlt.le hlast
      rwa [H.stageMetric_initial] at this
    have hmono : (β - 2 * C * ((u : ℝ) - H.time i.succ))⁻¹ ≤ (β - 2 * C * ((u : ℝ) - a))⁻¹ := by
      apply inv_anti₀ hden
      have : 2 * C * ((u : ℝ) - H.time i.succ) ≤ 2 * C * ((u : ℝ) - a) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hout : metricScalarAt (H.event i).outputMetric (A.point i.succ le_rfl hl) ≤
        (β - 2 * C * ((u : ℝ) - a))⁻¹ := by
      rw [H.event_output i]; exact hq0.trans hmono
    obtain ⟨p', hp', hbd⟩ := event_step_nc_S138 i (M := M) (β := β) (C := C) (u := u)
      (a0 := (a : ℝ)) (θ := θ) hC hβ hβM
      (fun t ht => hθ t (ht.2.le.trans hlast)) (hP2e i) hlast hlt hden _ hq0
      (hcross i hf hl A hout)
    refine ⟨p', hp', fun t ht hat _ => ?_⟩
    have ht' : t ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
      simpa [ObservedHistory.stageDomain] using ht
    exact hbd t ht' hat
  obtain ⟨X, hX⟩ := exists_backwardTrace_of_step_tr_S138 H Good (H.activeStage_mono hau) hy hstep
  refine ⟨X, fun w haw hwu => ?_⟩
  exact hX (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwu) w
    (H.activeStage_mem w) haw hwu

end GC.LongTime.Ch12
