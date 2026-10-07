import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84EventStep_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84TopStage_S74

/-!
# CH12-S74 G2 (b1'), assembly: the backward trace of `x0` with the scalar barrier on the window

`exists_trace_scalar_bound_S74`: on a history `H`, for a regular time `u` and `a ≤ u`, if the scalar at
`x0` (time `u`, active stage) is `< β⁻¹` and `(β - 2C(u - a))⁻¹ < C₁²/(4 r0²)`, every event of the
window has the cap exclusion data (`hscale`, `hrc`, `hnom`) and `θ ≤ M`, `β M < 1`, `P2` on the slabs,
then the backward trace `X` of `x0` over `[a, u]` exists and along it, at every `w ∈ [a, u]`,
`R(stageMetric (activeStage w) w)(X(w)) ≤ (β - 2C(u - w))⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace GC.LongTime.Ch12

universe u

theorem time_mem_stageDomain_S74 (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) :
    H.time j ∈ H.stageDomain j := by
  induction j using Fin.lastCases with
  | last => simpa [ObservedHistory.stageDomain] using H.time_le_horizon
  | cast i =>
    simpa [ObservedHistory.stageDomain] using H.time_strictMono (Fin.castSucc_lt_succ (i := i))

theorem exists_trace_scalar_bound_S74 (H : ObservedHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p)
    {C₁ r0 M β C : ℝ} {θ : ℝ → ℝ} (hC : 0 < C) (hβ : 0 < β) (hβM : β * M < 1) (hC₁ : 0 < C₁)
    (hr0 : 0 < r0)
    (hscale : ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((records i).static b).neck.scale / 2 ≤
        metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
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
    (hcapB : (β - 2 * C * ((u : ℝ) - a))⁻¹ < C₁ ^ 2 / (4 * r0 ^ 2))
    (hrc : ∀ i : Fin H.eventCount, H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage u →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hnom : ∀ i : Fin H.eventCount, H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage u →
      ∀ h, C₁ * (records i).nominalRadius h ≤ r0)
    (x0 : (H.stage (H.activeStage u)).Carrier)
    (hx0 : metricScalarAt (H.stageMetric (H.activeStage u) u) x0 < β⁻¹) :
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
  have hstep : ∀ i : Fin H.eventCount, H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage u →
      ∀ q : (H.stage i.succ).Carrier, Good i.succ q →
        ∃ p' : (H.stage i.castSucc).Carrier, (H.event i).RegularCrossing p' q ∧
          Good i.castSucc p' := by
    intro i hf hl q hq
    have hlast : H.time i.succ ≤ (u : ℝ) :=
      (H.time_strictMono.monotone hl).trans (H.activeStage_time_le u)
    have hlt : (a : ℝ) < H.time i.succ := by
      by_contra hn
      rw [not_lt] at hn
      have h1 : i.succ ≤ H.activeStage a := H.le_activeStage a _ hn
      exact absurd (hf.trans_lt (Fin.castSucc_lt_succ (i := i))) (not_lt.mpr h1)
    have hq0 : metricScalarAt (H.initialMetric i.succ) q ≤
        (β - 2 * C * ((u : ℝ) - H.time i.succ))⁻¹ := by
      have := hq (H.time i.succ) (time_mem_stageDomain_S74 H i.succ) hlt.le hlast
      rwa [H.stageMetric_initial] at this
    obtain ⟨p', hp', hbd⟩ := event_step_S74 i (records i) (M := M) (β := β) (C := C) (u := u)
      (a0 := (a : ℝ)) (θ := θ) hC hβ hβM hC₁ hr0 (hscale i) (hrc i hf hl) (hnom i hf hl)
      (fun t ht => hθ t (ht.2.le.trans hlast)) (hP2e i) hlast hlt hden hcapB q hq0
    refine ⟨p', hp', fun t ht hat _ => ?_⟩
    have ht' : t ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
      simpa [ObservedHistory.stageDomain] using ht
    exact hbd t ht' hat
  obtain ⟨X, hX⟩ := exists_backwardTrace_of_step_S74 H Good (H.activeStage_mono hau) hy hstep
  refine ⟨X, fun w haw hwu => ?_⟩
  have := hX (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwu) w
    (H.activeStage_mem w) haw hwu
  exact this

end GC.LongTime.Ch12
