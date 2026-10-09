import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBarrier_S88
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedFromSeeds_S43

/-!
# CH12-S88, group 1b: `traced_of_seeds_S43` with the per-event barrier instead of `δ`, `hnom`

`traced_of_seeds_barrier_S88` = `traced_of_seeds_S43` with the two cutoff hypotheses
(`δ ≤ 1/8646`, `Λ · nominalRadius ≤ r` for all events of the window) replaced by the barrier of each
event of the window on the slice's tower history (`TracedBarrier_S88`).  The window events are exactly
those with time in `(s.time - τ r², s.time]`; the barrier is asked only for them, and only for outgoing
connected low-scalar sets (`≤ 9 K₀ / r²`) anchored at a regular crossing.  The constants `Λ`, `hKΛ`
disappear.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem slice_seed_tracedRegion_barrier_S88
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation)
    {a : Icc (0 : ℝ) s.history.horizon} {τ r K : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K) (hexp : Real.exp (9 * K * τ) < 2)
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
    (hbar : ∀ i : Fin (sliceTowerHistory_CX2 s).eventCount,
      (sliceTowerHistory_CX2 s).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
      ∀ U : Set ((sliceTowerHistory_CX2 s).stage i.succ).Carrier, IsPreconnected U →
      (∀ y ∈ U, metricScalarAt ((sliceTowerHistory_CX2 s).event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : ((sliceTowerHistory_CX2 s).event i).incoming.terminalRegularOpen)
        (y : ((sliceTowerHistory_CX2 s).stage i.succ).Carrier),
        y ∈ U → ((sliceTowerHistory_CX2 s).event i).RegularCrossing x.val y →
        U ⊆ interior (range ((sliceTowerHistory_CX2 s).event i).oldOutput)) :
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
  have htr := record_seed_tracedRegion_barrier_S88 H hτ hr hK hexp (a := a') (t := t') ha hat
    hregular hy' Y' hbound' (fun i hf hl => hbar i (hevent i hf hl))
  exact (slice_isTracedRegion_iff_CX2 s (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (K / r ^ 2)).mpr htr

theorem traced_of_seeds_barrier_S88 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ (s : RegularSlice F.observation) (l : Icc (0 : ℝ) s.history.horizon)
        (_ : l ≤ sliceTop_S8 s) (y : (s.history.stageAt (sliceTop_S8 s)).Carrier)
        (r τ : ℝ), 0 < r → 0 < τ →
        Real.exp (9 * K₀ * τ) < 2 → l.val = s.time - τ * r ^ 2 →
      (∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v →
        T₀ ≤ (v : ℝ) ∧ r ≤ ρ₀ * Real.sqrt v) →
      (∀ (v : Icc (0 : ℝ) s.history.horizon) (_ : l ≤ v),
        ∃ yv : (s.history.stageAt v).Carrier,
          hasSmallParabolicCurvature s.history v yv (a * r) ∧
          ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
            ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
          ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
              (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono
                (show v ≤ sliceTop_S8 s from v.property.2)) y,
            A.point (s.history.activeStage v) le_rfl
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) →
      (∀ i : Fin (sliceTowerHistory_CX2 s).eventCount,
        (sliceTowerHistory_CX2 s).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
        ∀ U : Set ((sliceTowerHistory_CX2 s).stage i.succ).Carrier, IsPreconnected U →
        (∀ y ∈ U, metricScalarAt ((sliceTowerHistory_CX2 s).event i).outputMetric y ≤
          (9 * K₀) / r ^ 2) →
        ∀ (x : ((sliceTowerHistory_CX2 s).event i).incoming.terminalRegularOpen)
          (y : ((sliceTowerHistory_CX2 s).stage i.succ).Carrier),
          y ∈ U → ((sliceTowerHistory_CX2 s).event i).RegularCrossing x.val y →
          U ⊆ interior (range ((sliceTowerHistory_CX2 s).event i).oldOutput)) →
      s.history.isTracedRegion (sliceTop_S8 s) y (2 * r) (τ * r ^ 2) (K₀ / r ^ 2) := by
  obtain ⟨T₀, ρ₀, K₀, hT, hρ, hK, henl⟩ := enlarged_rm_bound_along_seed_trace_CX2 Hp ha hc₁
  refine ⟨T₀, ρ₀, K₀, hT, hρ, hK, ?_⟩
  intro s l hlt y r τ hr hτ hexp hl hsize hseed hbar
  obtain ⟨A, hA⟩ := henl s l hlt y r hr hsize hseed
  exact slice_seed_tracedRegion_barrier_S88 s hτ hr hK hexp hl hlt
    (mem_riemannianBallOf_self_O13 _ y hr) A (fun v hav _ q hq => hA v hav q hq) hbar

end GC.LongTime.Ch12
