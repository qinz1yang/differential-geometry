import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84CapExclude_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization

/-!
# CH12-O70 G1: single-event surgery exclusion with an explicit numeric budget

`[FROZEN v2] CH12-O70 G1`.  The surgery threshold of an event is read off the record: a cap point
of event `j` has output scalar `≥ C₀² / (4 r²)` as soon as `C₀ * nominalRadius ≤ r`
(`cap_scalar_ge_of_nominal_S74`).  The numeric budget of R5 (4) — `B / r²` below that threshold —
is the explicit condition `4 * B < C₀ ^ 2` (paid by `C ≥ C₀` in the late-`C` order).  Hence:

* `regularCrossing_of_budget_O70`: an output point with `R ≤ B / r²` is a regular-crossing image;
* `ball_subset_interior_range_O70`: an output ball on which `R ≤ B / r²` lies in the interior of
  the image of the old (pre-surgery) region, i.e. the event does not cut it (the conclusion of the
  S113 / S130 `hbar` barrier, with no connectedness / crossing premise needed).
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian

namespace GC.LongTime.Ch12

universe u

/-- R5 (4), single event: `R ≤ B / r²` and `4 B < C₀²` put the point below the cap threshold
`C₀² / (4 r²)`, so it has a regular-crossing preimage. -/
theorem regularCrossing_of_budget_O70 {H : ObservedHistory.{u}} {j : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H j p) {C₀ B r : ℝ} (hC₀ : 0 < C₀)
    (hr : 0 < r) (hbud : 4 * B < C₀ ^ 2)
    (hscale : ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      (R.static b).neck.scale / 2 ≤
        metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z))
    (hrc : p.recenterConstant * p.delta (H.time j.succ) ≤ 1 / 2)
    (hnom : ∀ h, C₀ * R.nominalRadius h ≤ r)
    (q : (H.stage j.succ).Carrier)
    (hq : metricScalarAt (H.event j).outputMetric q ≤ B / r ^ 2) :
    ∃ p' : (H.stage j.castSucc).Carrier, (H.event j).RegularCrossing p' q := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hlt : B / r ^ 2 < C₀ ^ 2 / (4 * r ^ 2) := by
    rw [div_lt_div_iff₀ hr2 (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hbud) hr2]
  exact exists_regularCrossing_of_scalar_lt_S74 R hC₀ hr hscale hrc hnom q (lt_of_le_of_lt hq hlt)

/-- R5 (4), single event, ball form: an output ball on which `R ≤ B / r²` (with `4 B < C₀²`) lies
in the interior of the image of the old region. -/
theorem ball_subset_interior_range_O70 {H : ObservedHistory.{u}} {j : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H j p) {C₀ B r : ℝ} (hC₀ : 0 < C₀)
    (hr : 0 < r) (hbud : 4 * B < C₀ ^ 2)
    (hscale : ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
      (R.static b).neck.scale / 2 ≤
        metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z))
    (hrc : p.recenterConstant * p.delta (H.time j.succ) ≤ 1 / 2)
    (hnom : ∀ h, C₀ * R.nominalRadius h ≤ r)
    (c : (H.stage j.succ).Carrier) {ρ : ℝ}
    (hball : ∀ q ∈ riemannianBallOf (H.event j).outputMetric c ρ,
      metricScalarAt (H.event j).outputMetric q ≤ B / r ^ 2) :
    riemannianBallOf (H.event j).outputMetric c ρ ⊆ interior (range (H.event j).oldOutput) := by
  apply interior_maximal _ (isOpen_riemannianBallOf _ c ρ)
  intro q hq
  obtain ⟨p', hcross⟩ := regularCrossing_of_budget_O70 R hC₀ hr hbud hscale hrc hnom q (hball q hq)
  obtain ⟨x, -, -, hx⟩ := hcross
  exact ⟨x, hx⟩

end GC.LongTime.Ch12
