import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HScale_S108

/-!
# CH12-S119, group 2: the `hscale` binders in their EXACT `scale / 2` text, from the profile clause `hprof`

S108 (G2) concluded that the exact `scale / 2 ≤ metricScalarAt witness.metric (witness.cap z)` text of the three
`hscale` binders (S94 `hsub86N_S94`, S89 `hlift_Ioo_of_Ico_S89`, MicroGlueLateRecords:421) is not provable
("only the abstract constant `c_std`").  That was wrong: the repo already proves it,
`exists_presented_cap_scalar_lower_bound_of_canonical_window_core` (Surgery/Topology/CanonicalCapScalar.lean:70;
via `StandardCap.exists_uniform_window_scalar_bounds_of_metric_close`, `1/2 < metricScalarAt g x` for
`‖x‖ ≤ transitionEnd`), with `ε₀` depending only on `Dstar`; the cap points `witness.cap z` are window points with
`‖x‖ ≤ transitionEnd` (third conjunct of `hasCanonicalWindow`).  The MicroGlue files already use it
(MicroGlueLateRecords:1048, :1568, MicroGlueTerminalLocal:376) to build the binder.

Hence no `c₀ * scale` rewrite of the consumers is needed: the only missing input is the parameter clause
`[FROZEN] CH12-S119 hprof` (D4 of S108):
`Hp.parameters.modelAccuracy ≤ ε₀ ∧ 2 ≤ Hp.parameters.modelOrder ∧ transitionEnd + 1 ≤ Hp.parameters.modelRadius`
with `ε₀ := hscale_of_prof_S119`'s absolute constant.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Record form, exact text: for every record whose parameters satisfy `modelAccuracy ≤ ε₀`, `2 ≤ modelOrder`,
`transitionEnd + 1 ≤ modelRadius` (the `hprof` clause) and which has canonical windows. -/
theorem hscale_record_exact_S119 : ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀ → 2 ≤ pp.modelOrder → StandardCap.transitionEnd + 1 ≤ pp.modelRadius →
      ∀ (R : GeometricCutoffRecord H i pp) (b : (H.event i).RetainedBoundaryIndex),
        (R.static b).hasCanonicalWindow → ∀ z : ThreeBall,
          (R.static b).neck.scale / 2 ≤
            metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
    (StandardCap.transitionEnd + 1) (lt_add_one _)
  refine ⟨ε₀, hε₀, ?_⟩
  intro H pp i hε hm hD R b hcan z
  exact h (H.event i) hD hε hm (R.static b) hcan z

/-- Profile form, exact text of the S94 / S89 / S72 / O42 `hscale` binder: under the `hprof` clause
`modelAccuracy ≤ ε₀ ∧ 2 ≤ modelOrder ∧ transitionEnd + 1 ≤ modelRadius` (ε₀ absolute), every record of the
profile has cap scalar `≥ scale / 2` (canonical windows = `Hp.canonical_windows`). -/
theorem hscale_of_prof_S119 : ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
      (Hp : AnalyticSurgeryProfile F δ),
      (Hp.parameters.modelAccuracy ≤ ε₀ ∧ 2 ≤ Hp.parameters.modelOrder ∧
        StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) →
      ∀ n (i : Fin (F.tower.history n).eventCount)
        (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((Hp.records n i).static b).neck.scale / 2 ≤
          metricScalarAt ((Hp.records n i).static b).witness.metric
            (((Hp.records n i).static b).witness.cap z) := by
  obtain ⟨ε₀, hε₀, h⟩ := hscale_record_exact_S119.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ Hp ⟨hε, hm, hD⟩ n i b z
  exact h hε hm hD (Hp.records n i) b (Hp.canonical_windows n i b) z

end GC.LongTime.Ch12
