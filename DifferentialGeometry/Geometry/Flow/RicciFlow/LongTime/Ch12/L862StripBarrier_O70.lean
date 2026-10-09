import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862StripEvent_O70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathAlgebra_CX2

/-!
# CH12-O70 G2: no surgery cuts the 84.1 ball along the seed strip (`[FROZEN v2] CH12-O70 G2-out`)

Input `hBig` = the scalar conjunct of `[FROZEN] CH12-O69 G1-out` (with `ρ := A r`): `R ≤ B / r²`
on the moving balls `B_w(Y(w), ρ)` of the seed strip `[a', a]`.  On a window `[ae, a]` (`a' ≤ ae`)
whose events satisfy the cutoff budget `C₀ * nominalRadius ≤ r` with `4 B < C₀²`, every event `i`
of the window leaves the output ball `B_out(Y(i.succ), ρ)` inside the interior of the image of the
old region (`strip_barrier_O70`; each event is handled by the single-event lemma of G1 at the event
time `e = time i.succ`, where `activeStage e = i.succ` and `stageMetric i.succ e = outputMetric`).
`strip_hbar_O70` restates this as the `hbar` binder of `traced_family_of_trace_S130` (S113 barrier
shape) along the seed centre line restricted to `[ae, a]`, for every `r'` with `20 r' ≤ ρ`.
`strip_barrier_slice_O70` is the tower-slice instance (records of `AnalyticSurgeryProfile`,
`hscale` / `hrc` in the shapes of `hscale_of_prof_S119` / `hrc_of_hdec_S118`, `hnom` in the
frozen hU shape).
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian

namespace GC.LongTime.Ch12

universe u

/-- **G2-out.**  Along the seed strip, no event of the window `[ae, a]` cuts the 84.1 ball:
every subset of the output ball `B_out(Y(i.succ), ρ)` lies in the interior of the old image. -/
theorem strip_barrier_O70 (H : ObservedHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p)
    {B C₀ r ρ : ℝ} (hC₀ : 0 < C₀) (hr : 0 < r) (hbud : 4 * B < C₀ ^ 2)
    (hscale : ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((records i).static b).neck.scale / 2 ≤
        metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    {a' ae a : Icc (0 : ℝ) H.horizon} (ha'e : a' ≤ ae) (hea : ae ≤ a)
    (hrc : ∀ i : Fin H.eventCount, H.time i.succ ∈ Icc (ae : ℝ) a →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hnom : ∀ i : Fin H.eventCount, H.time i.succ ∈ Icc (ae : ℝ) a →
      ∀ h, C₀ * (records i).nominalRadius h ≤ r)
    {y : (H.stageAt a).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a') (H.activeStage a)
      (H.activeStage_mono (ha'e.trans hea)) y)
    (hBig : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
          (Y.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwa)) ρ,
        metricScalarAt (H.stageMetric (H.activeStage w) w) q ≤ B / r ^ 2) :
    ∀ (i : Fin H.eventCount) (hf : H.activeStage ae ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage a) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ ((H.activeStage_mono ha'e).trans (hf.trans i.castSucc_lt_succ.le)) hl) ρ →
      U ⊆ interior (range (H.event i).oldOutput) := by
  intro i hf hl U hU
  let e : Icc (0 : ℝ) H.horizon := ⟨H.time i.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
  have hae : ae ≤ e :=
    (time_lt_of_activeStage_lt_CX2 H ae i.succ (hf.trans_lt i.castSucc_lt_succ)).le
  have het : e ≤ a := (H.time_strictMono.monotone hl).trans (H.activeStage_time_le a)
  have hej : H.activeStage e = i.succ := H.activeStage_at_time i.succ
  have hwin : H.time i.succ ∈ Icc (ae : ℝ) a := ⟨hae, het⟩
  have key : ∀ (j : Fin (H.eventCount + 1)) (hj : H.activeStage e = j)
      (h1 : H.activeStage a' ≤ j) (h2 : j ≤ H.activeStage a),
      ∀ q ∈ riemannianBallOf (H.stageMetric j e) (Y.point j h1 h2) ρ,
        metricScalarAt (H.stageMetric j e) q ≤ B / r ^ 2 := by
    intro j hj h1 h2
    subst hj
    exact hBig e (ha'e.trans hae) het
  have hball := key i.succ hej
    ((H.activeStage_mono ha'e).trans (hf.trans i.castSucc_lt_succ.le)) hl
  have hmetricE : H.stageMetric i.succ e = (H.event i).outputMetric :=
    (H.stageMetric_initial i.succ).trans (H.event_output i).symm
  rw [hmetricE] at hball
  exact hU.trans (ball_subset_interior_range_O70 (records i) hC₀ hr hbud (hscale i) (hrc i hwin)
    (hnom i hwin) _ hball)

/-- **G2-out, S130 form.**  The `hbar` binder of `traced_family_of_trace_S130` (ball-located
barrier at every event of `[ae, a]`), along the seed centre line restricted to `[ae, a]`, radius
`20 r'` with `20 r' ≤ ρ`, any `K`.  Its connectedness / scalar / crossing premises are not needed. -/
theorem strip_hbar_O70 (H : ObservedHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p)
    {B C₀ r ρ : ℝ} (hC₀ : 0 < C₀) (hr : 0 < r) (hbud : 4 * B < C₀ ^ 2)
    (hscale : ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((records i).static b).neck.scale / 2 ≤
        metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    {a' ae a : Icc (0 : ℝ) H.horizon} (ha'e : a' ≤ ae) (hea : ae ≤ a)
    (hrc : ∀ i : Fin H.eventCount, H.time i.succ ∈ Icc (ae : ℝ) a →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hnom : ∀ i : Fin H.eventCount, H.time i.succ ∈ Icc (ae : ℝ) a →
      ∀ h, C₀ * (records i).nominalRadius h ≤ r)
    {y : (H.stageAt a).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a') (H.activeStage a)
      (H.activeStage_mono (ha'e.trans hea)) y)
    (hBig : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
          (Y.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwa)) ρ,
        metricScalarAt (H.stageMetric (H.activeStage w) w) q ≤ B / r ^ 2)
    {r' K : ℝ} (h20 : 20 * r' ≤ ρ) :
    ∀ (i : Fin H.eventCount) (hf : H.activeStage ae ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage a) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric
        ((Y.restrictFirst (H.activeStage_mono ha'e) (H.activeStage_mono hea)).point i.succ
          (hf.trans i.castSucc_lt_succ.le) hl) (20 * r') → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r' ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y →
          U ⊆ interior (range (H.event i).oldOutput) := by
  intro i hf hl U hU _ _ _ _ _ _
  exact strip_barrier_O70 H records hC₀ hr hbud hscale ha'e hea hrc hnom Y hBig i hf hl U
    (hU.trans fun q hq => lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal h20))

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **G2-out, tower-slice instance** on `N := sliceTowerHistory_CX2 s`: records of the profile,
`hscale` = conclusion of `hscale_of_prof_S119`, `hrc` = conclusion of `hrc_of_hdec_S118` at its
`Trc` (with `Trc ≤ ae`), `hnom` = the cutoff budget of the frozen hU (window `[ae, a]`). -/
theorem strip_barrier_slice_O70 (Hp : AnalyticSurgeryProfile F δ)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z))
    {Trc : ℝ}
    (hrc : ∀ n (i : Fin (F.tower.history n).eventCount),
      Trc ≤ (F.tower.history n).toHistory.time i.succ →
      Hp.parameters.recenterConstant *
        Hp.parameters.delta ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2)
    (s : RegularSlice F.observation) {B C₀ r ρ : ℝ} (hC₀ : 0 < C₀) (hr : 0 < r)
    (hbud : 4 * B < C₀ ^ 2)
    {a' ae a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon} (ha'e : a' ≤ ae) (hea : ae ≤ a)
    (hTrc : Trc ≤ (ae : ℝ))
    (hnom : ∀ m (i : Fin (F.tower.history m).eventCount),
      (F.tower.history m).time i.succ ∈ Icc (ae : ℝ) a →
      ∀ h, C₀ * (Hp.records m i).nominalRadius h ≤ r)
    {y : ((sliceTowerHistory_CX2 s).stageAt a).Carrier}
    (Y : BackwardPointTrace (sliceTowerHistory_CX2 s) ((sliceTowerHistory_CX2 s).activeStage a')
      ((sliceTowerHistory_CX2 s).activeStage a)
      ((sliceTowerHistory_CX2 s).activeStage_mono (ha'e.trans hea)) y)
    (hBig : ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a' ≤ w) (hwa : w ≤ a),
      ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage w) w)
          (Y.point ((sliceTowerHistory_CX2 s).activeStage w)
            ((sliceTowerHistory_CX2 s).activeStage_mono haw)
            ((sliceTowerHistory_CX2 s).activeStage_mono hwa)) ρ,
        metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage w) w) q ≤ B / r ^ 2) :
    ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount)
      (hf : (sliceTowerHistory_CX2 s).activeStage ae ≤ i.castSucc)
      (hl : i.succ ≤ (sliceTowerHistory_CX2 s).activeStage a)
      (U : Set ((sliceTowerHistory_CX2 s).stage i.succ).Carrier),
      U ⊆ riemannianBallOf ((sliceTowerHistory_CX2 s).event i).outputMetric
        (Y.point i.succ (((sliceTowerHistory_CX2 s).activeStage_mono ha'e).trans
          (hf.trans i.castSucc_lt_succ.le)) hl) ρ →
      U ⊆ interior (range ((sliceTowerHistory_CX2 s).event i).oldOutput) :=
  strip_barrier_O70 (sliceTowerHistory_CX2 s) (Hp.records (sliceTowerIndex_CX2 s)) hC₀ hr hbud
    (hscale (sliceTowerIndex_CX2 s)) ha'e hea
    (fun i hi => hrc (sliceTowerIndex_CX2 s) i (hTrc.trans hi.1))
    (fun i hi => hnom (sliceTowerIndex_CX2 s) i hi) Y hBig

end GC.LongTime.Ch12
