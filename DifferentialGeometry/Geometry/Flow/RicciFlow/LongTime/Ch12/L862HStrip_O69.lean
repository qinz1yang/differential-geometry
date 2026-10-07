import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84CapExclude_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathAlgebra_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HScaleExact_S119
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchWiringTail_S118

/-!
# CH12-O69 G3: the centre-free strip barrier `hStrip` of `hU_of_parts_O71`

`hStrip_O69 Hp hdec hprof : <hStrip>` (text = `hStrip` binder of `hU_of_parts_O71` =
`frozen_hStrip_O71`, `[FROZEN v2] CH12-O71 hStrip`).  For every event of `[ae, a]` on
`N := sliceTowerHistory_CX2 s`, every set `U` with `R ≤ 9B/r²` (output metric) lies in the interior
of the image of the old region: the open set `{R < C₀²/(4r²)}` contains `U` and, by the single-event
cap exclusion `exists_regularCrossing_of_scalar_lt_S74`, lies in `range oldOutput`.  `hscale` from
`hscale_of_prof_S119 … hprof`, `hrc` from `hrc_of_hdec_S118 Hp hdec`.  Constants:
`C₀ := 18 B + 2` (so `36 B < C₀²`), `b₂ := 1/2` (so event times are `≥ u/2`), `T₂ := 2 max Trc 1`.
The preconnectedness and crossing premises of the frozen shape are not needed.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal

namespace GC.LongTime.Ch12

universe u

/-- **G3** (O69): `hStrip` of `hU_of_parts_O71` from `hdec` and `hprof`. -/
theorem hStrip_O69 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) :
    ∀ B : ℝ, 0 < B → ∃ C₀ b₂ T₂ : ℝ, 1 ≤ C₀ ∧ 0 < b₂ ∧ 0 < T₂ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₂ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (r : ℝ), 0 < r → r ≤ b₂ * Real.sqrt u →
      ∀ (a ae : Icc (0 : ℝ) N.horizon), a ≤ u → (u : ℝ) - 2 * r ^ 2 ≤ ae → ae ≤ a →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc (ae : ℝ) a →
          ∀ h, C₀ * (Hp.records m i).nominalRadius h ≤ r) →
        ∀ (i : Fin N.eventCount) (_hf : N.activeStage ae ≤ i.castSucc)
          (_hl : i.succ ≤ N.activeStage a) (U : Set (N.stage i.succ).Carrier),
          IsPreconnected U →
          (∀ y ∈ U, metricScalarAt (N.event i).outputMetric y ≤ 9 * B / r ^ 2) →
          ∀ (x : (N.event i).incoming.terminalRegularOpen) (y : (N.stage i.succ).Carrier),
            y ∈ U → (N.event i).RegularCrossing x.val y →
            U ⊆ interior (range (N.event i).oldOutput) := by
  intro B hB
  obtain ⟨Trc, hrc⟩ := hrc_of_hdec_S118 Hp hdec
  have hscale := (hscale_of_prof_S119.{u}).choose_spec.2 Hp hprof
  have hT1 : (1 : ℝ) ≤ max Trc 1 := le_max_right _ _
  refine ⟨18 * B + 2, 1 / 2, 2 * max Trc 1, by linarith, by norm_num, by positivity, ?_⟩
  intro s N u hTu _hus r hr hrb a ae _hau hue hea hnom i hf hl U _hpre hUR _x _y _hy _hcr
  have hC₀ : (0 : ℝ) < 18 * B + 2 := by linarith
  -- the event time lies in `[ae, a]` and above `Trc`
  have hae : (ae : ℝ) ≤ N.time i.succ :=
    (time_lt_of_activeStage_lt_CX2 N ae i.succ (hf.trans_lt i.castSucc_lt_succ)).le
  have het : N.time i.succ ≤ (a : ℝ) :=
    (N.time_strictMono.monotone hl).trans (N.activeStage_time_le a)
  have hwin : N.time i.succ ∈ Icc (ae : ℝ) a := ⟨hae, het⟩
  have hu0 : (0 : ℝ) ≤ u := u.2.1
  have hr2 : r ^ 2 ≤ u / 4 := by
    have h1 : r ^ 2 ≤ (1 / 2 * Real.sqrt u) ^ 2 := pow_le_pow_left₀ hr.le hrb 2
    rw [mul_pow, Real.sq_sqrt hu0] at h1
    linarith
  have hTrc : Trc ≤ N.time i.succ := by
    have h1 : Trc ≤ max Trc 1 := le_max_left _ _
    have h2a : max Trc 1 ≤ (u : ℝ) / 2 := by linarith [hTu]
    have h2b : (u : ℝ) / 2 ≤ (u : ℝ) - 2 * r ^ 2 := by linarith [hr2]
    have h2 : max Trc 1 ≤ (ae : ℝ) := h2a.trans (h2b.trans hue)
    exact h1.trans (h2.trans hae)
  have hrc' := hrc (sliceTowerIndex_CX2 s) i hTrc
  -- the open sublevel set below the cap threshold lies in the old image
  have hlt : 9 * B / r ^ 2 < (18 * B + 2) ^ 2 / (4 * r ^ 2) := by
    have hrr : 0 < r ^ 2 := by positivity
    rw [div_lt_div_iff₀ hrr (by positivity)]
    have key : 36 * B < (18 * B + 2) ^ 2 := by nlinarith [hB, sq_nonneg (18 * B)]
    calc 9 * B * (4 * r ^ 2) = 36 * B * r ^ 2 := by ring
      _ < (18 * B + 2) ^ 2 * r ^ 2 := mul_lt_mul_of_pos_right key hrr
  have hopen : IsOpen {q : (N.stage i.succ).Carrier |
      metricScalarAt (N.event i).outputMetric q < (18 * B + 2) ^ 2 / (4 * r ^ 2)} :=
    isOpen_lt (metricScalar_smooth _).continuous continuous_const
  have hsub : {q : (N.stage i.succ).Carrier |
      metricScalarAt (N.event i).outputMetric q < (18 * B + 2) ^ 2 / (4 * r ^ 2)} ⊆
      range (N.event i).oldOutput := by
    intro q hq
    obtain ⟨p', hcross⟩ := exists_regularCrossing_of_scalar_lt_S74
      (Hp.records (sliceTowerIndex_CX2 s) i) hC₀ hr (hscale (sliceTowerIndex_CX2 s) i) hrc'
      (hnom (sliceTowerIndex_CX2 s) i hwin) q hq
    obtain ⟨x, -, -, hx⟩ := hcross
    exact ⟨x, hx⟩
  intro z hz
  exact interior_maximal hsub hopen (lt_of_le_of_lt (hUR z hz) hlt)

end GC.LongTime.Ch12
