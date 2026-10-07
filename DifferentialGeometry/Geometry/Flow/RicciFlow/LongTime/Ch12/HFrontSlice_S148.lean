import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HDist_S108
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSAssembly_S113

/-!
# CH12-S148: slice adapter for `hFront` (`hFront_of_collar_S95` + `rfcB_S108`)

`hFront_S148 Hp hRFCa` is the `hFront` binder of `hTS_S113` / `hFEcore_S138` / `hFE_S138` (S95 text on the records of
the slice history, `Dc := Dcap - 1`), with RFC-b discharged by `rfcB_S108` (collar distance `hdist` built in) and
RFC-a the single remaining input, a ch11 record clause (`[FROZEN] CH12-S105 RFC-a`, slice-quantified; see
`[FROZEN] CH12-S148 hFront`).  The record premises of RFC-b (`hlink`, `hacc`, `hDc`, `hD`) are all inside the binder:
`hlink` is a hypothesis of the binder, `hacc` from `εFr := 3/4`, `hDc` from `transitionEnd + 3 < Dcap`, `hD` from
`32 (Dcap + 1) + 2 ≤ modelRadius`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem hFront_S148 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hRFCa : ∀ (s : RegularSlice F.observation) (pp : CutoffParameters),
      pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
      pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
      StandardCap.transitionEnd + 3 < pp.modelRadius → pp.modelAccuracy ≤ 3 / 4 →
      4 ≤ pp.modelOrder →
      ∀ (i : Fin (sliceHistoryR_O3 F s).eventCount)
        (R : GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        (∀ b, linkedCanonicalWindow_O2 (R.static b)) →
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event i).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event i).RetainedBoundaryIndex)
            (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 ∧
              (R.static b).inclusion ((R.static b).witness.retained c) = y) :
    ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1 := by
  intro θ Dcap hDcap
  refine ⟨0, 3 / 4, by norm_num, ?_⟩
  intro s _ T₀ _ _ pp records h1 h2 h3 h4 hrad hacc hord hlink j hj
  have hte : 0 < StandardCap.transitionEnd := StandardCap.transitionEnd_pos
  have hD : StandardCap.transitionEnd + 3 < pp.modelRadius := by linarith
  exact hFront_of_collar_S95 (Dc := Dcap - 1) (records j hj)
    (hRFCa s pp h1 h2 h3 h4 hD hacc hord j (records j hj) (hlink j hj))
    (fun b cc hcc => rfcB_S108 (records j hj) b (hlink j hj b) hacc (by linarith) hD cc hcc)

end GC.LongTime.Ch12
