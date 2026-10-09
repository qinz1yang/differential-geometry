import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBallPath_S88
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedLocalSeeds_S88

/-!
# CH12-S95, group 1: slice / `traced_of_seeds` with the ball-located barrier

`slice_seed_tracedRegion_ball_S95` and `traced_of_seeds_ball_S95` are `slice_seed_tracedRegion_barrier_S88`
and `traced_of_seeds_barrier_S88` (TracedLocalSeeds_S88) with the event barrier asked only for sets `U`
inside the `20 r`-ball (post-event metric) about the trace point `Y'.point i.succ` of the centre
(`record_seed_tracedRegion_ball_S88`, TracedBallPath_S88), where `Y'` is the trace of the centre in the
slice's tower history.
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

theorem slice_seed_tracedRegion_ball_S95
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
    (hbar : ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount)
      (hf : (sliceTowerHistory_CX2 s).activeStage
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) a) ≤ i.castSucc)
      (hl : i.succ ≤ (sliceTowerHistory_CX2 s).activeStage
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s))),
      (sliceTowerHistory_CX2 s).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
      ∀ U : Set ((sliceTowerHistory_CX2 s).stage i.succ).Carrier,
      U ⊆ riemannianBallOf ((sliceTowerHistory_CX2 s).event i).outputMetric
        ((traceAtOfRestriction_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (hat := hat) Y).point
          i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) → IsPreconnected U →
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
  have htr := record_seed_tracedRegion_ball_S88 H hτ hr hK hexp (a := a') (t := t') ha hat
    hregular hy' Y' hbound' (fun i hf hl U hUb => hbar i hf hl (hevent i hf hl) U hUb)
  exact (slice_isTracedRegion_iff_CX2 s (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (K / r ^ 2)).mpr htr

theorem traced_of_seeds_ball_S95 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ (s : RegularSlice F.observation) (l : Icc (0 : ℝ) s.history.horizon)
        (hlt : l ≤ sliceTop_S8 s) (y : (s.history.stageAt (sliceTop_S8 s)).Carrier)
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
      (∀ A : BackwardPointTrace s.history (s.history.activeStage l)
          (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hlt) y,
        (∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : l ≤ v) (hvt : v ≤ sliceTop_S8 s),
          ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
            (A.point (s.history.activeStage v) (s.history.activeStage_mono hav)
              (s.history.activeStage_mono hvt)) (20 * r),
          Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
            (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2) →
        ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount)
          (hf : (sliceTowerHistory_CX2 s).activeStage
            (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) l) ≤ i.castSucc)
          (hl : i.succ ≤ (sliceTowerHistory_CX2 s).activeStage
            (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s))),
          (sliceTowerHistory_CX2 s).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
          ∀ U : Set ((sliceTowerHistory_CX2 s).stage i.succ).Carrier,
          U ⊆ riemannianBallOf ((sliceTowerHistory_CX2 s).event i).outputMetric
            ((traceAtOfRestriction_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s)
              (hat := hlt) A).point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) →
          IsPreconnected U →
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
  have hA' : ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : l ≤ v) (hvt : v ≤ sliceTop_S8 s),
      ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
        (A.point (s.history.activeStage v) (s.history.activeStage_mono hav)
          (s.history.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
        (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2 :=
    fun v hav hvt q hq => hA v hav q hq
  exact slice_seed_tracedRegion_ball_S95 s hτ hr hK hexp hl hlt
    (mem_riemannianBallOf_self_O13 _ y hr) A hA' (fun i hf hl' ht U hU => hbar A hA' i hf hl' ht U hU)

end GC.LongTime.Ch12
