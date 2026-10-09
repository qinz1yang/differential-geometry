import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceG3b_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedPath_CX2

/-!
# CH12-S43, group 2: the traced backward region from seeds, with the cutoff-radius hypotheses
restricted to the backward window

CX2's `slice_seed_tracedRegion_CX2` asks `δ ≤ 1/8646` and `Λ · nominalRadius ≤ r` for ALL events
with time in `[t/2, t]`.  At micro test balls that is false (`ρ < Λ_micro · nominalRadius` of a
recent event).  Only events CROSSED by the trace, i.e. with time in `(t - τ r², t]`, enter the
proof (`record_seed_tracedRegion_CX2` takes `hδ`, `hnom` exactly for crossed events), so here both
hypotheses are asked for events with time in `Ioc (t - τ r²) t`.
* `slice_seed_tracedRegion_window_S43`: the window-restricted form of `slice_seed_tracedRegion_CX2`
  (same proof).
* `traced_of_seeds_S43`: per-time seeds along the window (the CX2 / G2 shape of
  `enlarged_rm_bound_along_seed_trace_CX2`) ⇒ the traced region `isTracedRegion t y (2r) (τ r²) (K₀/r²)`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem slice_seed_tracedRegion_window_S43
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    {a : Icc (0 : ℝ) s.history.horizon} {τ r K Λ : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K) (hΛ : 1 ≤ Λ)
    (hKΛ : 2 * (9 * K) < Λ ^ 2) (hexp : Real.exp (9 * K * τ) < 2)
    (ha : a.val = s.time - τ * r ^ 2) (hat : a ≤ sliceTop_S8 s)
    {p y : (s.history.stageAt (sliceTop_S8 s)).Carrier}
    (hy : y ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r)
    (Y : BackwardPointTrace s.history (s.history.activeStage a)
      (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) y)
    (hbound : ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a ≤ v) (hvt : v ≤ sliceTop_S8 s),
      ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
        (Y.point (s.history.activeStage v) (s.history.activeStage_mono hav) (s.history.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
        (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K / r ^ 2)
    (hδ : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
      ∀ j, (Hp.records n i).delta j ≤ 1 / 8646)
    (hnom : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
      ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) :
    s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (K / r ^ 2) := by
  let H := sliceTowerHistory_CX2 s
  let cut := sliceTowerTime_CX2 s
  let a' := restrictTime_CX2 H cut a
  let t' := restrictTime_CX2 H cut (sliceTop_S8 s)
  let Y' := traceAtOfRestriction_CX2 H cut (hat := hat) Y
  have hbound' := seed_trace_ball_bound_of_restriction_CX2 H cut (hat := hat) Y hbound
  have hy' := (metricBall_heq_CX2 (H.restrict_stageAt cut (sliceTop_S8 s))
    (H.restrict_sliceMetric cut (sliceTop_S8 s))
    (restrictPoint_heq_CX2 H cut (sliceTop_S8 s) p).symm
    (restrictPoint_heq_CX2 H cut (sliceTop_S8 s) y).symm r).mp hy
  have hregular : H.time (H.activeStage t') < t'.val := s.preceding
  have hevent (i : Fin H.eventCount) (hf : H.activeStage a' ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t') :
      H.time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time := by
    have h := (H.crossed_event_iff_mem_Ioc a' t' i).mp ⟨hf, hl⟩
    refine ⟨?_, h.2⟩
    have h1 := h.1
    change a.val < _ at h1
    rw [ha] at h1
    exact h1
  have htr := record_seed_tracedRegion_CX2 H Hp.parameters (Hp.records (sliceTowerIndex_CX2 s))
    hτ hr hK hΛ hKΛ hexp (a := a') (t := t') ha hat hregular hy' Y' hbound'
    (fun i hf hl => hδ (sliceTowerIndex_CX2 s) i (hevent i hf hl))
    (fun i hf hl => hnom (sliceTowerIndex_CX2 s) i (hevent i hf hl))
  exact (slice_isTracedRegion_iff_CX2 s (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (K / r ^ 2)).mpr htr

end GC.LongTime.Ch12
