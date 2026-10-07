import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceRestrictionBack_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsEnlarge_O4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MacroWholeBallWbd01

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- The entire parabolic seed, including its traces through surgery seams,
lifts to the history of which it is an actual prefix. -/
theorem smallParabolicCurvature_of_restriction_CX2 (H : ObservedHistory.{u})
    (cut : Icc (0 : ℝ) H.horizon) (t : Icc (0 : ℝ) (H.restrict cut).horizon)
    (p : ((H.restrict cut).stageAt t).Carrier) {r : ℝ}
    (hseed : hasSmallParabolicCurvature (H.restrict cut) t p r) :
    hasSmallParabolicCurvature H (restrictTime_CX2 H cut t) (restrictPoint_CX2 H cut t p) r := by
  obtain ⟨hr, a, hat, ha, htrace⟩ := hseed
  refine ⟨hr, restrictTime_CX2 H cut a, hat, ha, ?_⟩
  intro x hx
  obtain ⟨x', rfl⟩ := restrictPoint_surjective_CX2 H cut t x
  have hx' := (metricBall_heq_CX2 (H.restrict_stageAt cut t) (H.restrict_sliceMetric cut t)
    (restrictPoint_heq_CX2 H cut t p).symm (restrictPoint_heq_CX2 H cut t x').symm r).mpr hx
  obtain ⟨A, hA⟩ := htrace x' hx'
  let B := traceAtOfRestriction_CX2 H cut (hat := hat) A
  have hscale : 0 < Real.sqrt 3 * r := mul_pos (by positivity) hr
  refine ⟨B, (B.isRmControlled_iff_isRmBoundedBy hscale).mpr ?_⟩
  exact traceAtOfRestriction_bounded_CX2 H cut A
    ((A.isRmControlled_iff_isRmBoundedBy hscale).mp hA)

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- The tower index actually used by `observe`. -/
def sliceTowerIndex_CX2 (s : RegularSlice F.observation) : ℕ := Nat.ceil s.time

def sliceTowerHistory_CX2 (s : RegularSlice F.observation) : ObservedHistory.{u} :=
  (F.tower.history (sliceTowerIndex_CX2 s)).toHistory

def sliceTowerTime_CX2 (s : RegularSlice F.observation) :
    Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon :=
  ⟨s.time, s.positive.le, by
    change s.time ≤ (F.tower.history (sliceTowerIndex_CX2 s)).horizon
    rw [F.tower.horizon_eq]
    exact Nat.le_ceil _⟩

/-- This equality uses the definition of observation; no unrelated history
with a matching horizon is substituted. -/
theorem slice_history_restrict_CX2 (s : RegularSlice F.observation) :
    s.history = (sliceTowerHistory_CX2 s).restrict (sliceTowerTime_CX2 s) := rfl

/-- The actual slice/tower equivalence of buffered traced regions. -/
theorem slice_isTracedRegion_iff_CX2 (s : RegularSlice F.observation)
    (t : Icc (0 : ℝ) s.history.horizon) (p : (s.history.stageAt t).Carrier) (ρ τ K : ℝ) :
    s.history.isTracedRegion t p ρ τ K ↔
      (sliceTowerHistory_CX2 s).isTracedRegion
        (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t)
        (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t p) ρ τ K :=
  isTracedRegion_restrict_iff_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) t p ρ τ K

/-- G3a on precisely the slice histories occurring in the frozen G2 input.
The constants remain uniform in the slice, its time, and the centre. -/
theorem enlarged_rm_bound_of_slice_seed_CX2 (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ s : RegularSlice F.observation,
      ∀ (v : Icc (0 : ℝ) s.history.horizon) (y : (s.history.stageAt v).Carrier) (r : ℝ),
        0 < r → T₀ ≤ (v : ℝ) → r ≤ ρ₀ * Real.sqrt v →
        hasSmallParabolicCurvature s.history v y (a * r) →
        ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
          ballVolume (s.history.stageMetric (s.history.activeStage v) v) y (a * r) →
        ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v) y (20 * r),
          Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
            (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2 := by
  obtain ⟨T₀, ρ₀, K₀, hT, hρ, hK, hbound⟩ := enlarged_rm_bound_of_seed_O4 Hp ha hc₁
  refine ⟨T₀, ρ₀, K₀, hT, hρ, hK, ?_⟩
  intro s v y r hr hTv hrv hseed hvol q hq
  let H := sliceTowerHistory_CX2 s
  let cut := sliceTowerTime_CX2 s
  have hs := smallParabolicCurvature_of_restriction_CX2 H cut v y hseed
  have hvolume := ballVolume_heq_CX2 (H.restrict_stageAt cut v) (H.restrict_sliceMetric cut v)
    (restrictPoint_heq_CX2 H cut v y).symm (a * r)
  have hv : ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage (restrictTime_CX2 H cut v)) v)
        (restrictPoint_CX2 H cut v y) (a * r) := hvol.trans_eq hvolume
  have hq' := (metricBall_heq_CX2 (H.restrict_stageAt cut v) (H.restrict_sliceMetric cut v)
    (restrictPoint_heq_CX2 H cut v y).symm (restrictPoint_heq_CX2 H cut v q).symm (20 * r)).mp hq
  have hb := hbound (sliceTowerIndex_CX2 s) (restrictTime_CX2 H cut v)
    (restrictPoint_CX2 H cut v y) r hr hTv hrv hs hv (restrictPoint_CX2 H cut v q) hq'
  have heq := rmNormSq_heq_CX2 (H.restrict_stageAt cut v) (H.restrict_sliceMetric cut v)
    (restrictPoint_heq_CX2 H cut v q).symm
  exact (congrArg Real.sqrt heq).trans_le hb

end GC.LongTime.Ch12
