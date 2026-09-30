import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation

set_option autoImplicit false

noncomputable section

open Set Filter Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem eventually_backwardSurvivor_scalar_close_and_edist_le (H : ObservedHistory.{u})
    (j : Fin H.eventCount) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ σ in 𝓝[<] H.time j.succ,
      (∀ x : H.backwardSurvivorDomain j.castSucc j.succ j.castSucc_lt_succ.le,
        |metricScalarAt ((H.event j).incoming.flow.base.metric σ)
            (H.backwardSurvivorMap j.castSucc j.succ j.castSucc_lt_succ.le j.castSucc le_rfl
              j.castSucc_lt_succ.le x) -
          metricScalarAt (H.initialMetric j.succ) x.val| < δ) ∧
      ∀ x z : H.backwardSurvivorDomain j.castSucc j.succ j.castSucc_lt_succ.le,
        riemannianEDistOf ((H.event j).incoming.flow.base.metric σ)
            (H.backwardSurvivorMap j.castSucc j.succ j.castSucc_lt_succ.le j.castSucc le_rfl
              j.castSucc_lt_succ.le x)
            (H.backwardSurvivorMap j.castSucc j.succ j.castSucc_lt_succ.le j.castSucc le_rfl
              j.castSucc_lt_succ.le z) ≤
          ENNReal.ofReal (Real.sqrt 2) *
            riemannianEDistOf ((H.initialMetric j.succ).restrictOpen
              (H.backwardSurvivorDomain j.castSucc j.succ j.castSucc_lt_succ.le)) x z := by
  have hle : j.castSucc ≤ j.succ := j.castSucc_lt_succ.le
  let U := H.backwardSurvivorDomain j.castSucc j.succ hle
  let E := H.event j
  let T := H.backwardSurvivorTerminalMap j.castSucc j.succ hle j le_rfl le_rfl
  let K : Set E.incoming.terminalRegularOpen := range E.oldTerminal
  have hK : IsCompact K := by
    have : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
    exact isCompact_range E.oldTerminal.continuous
  have hTK (x : U) : T x ∈ K := by
    obtain ⟨w, -, hw, -⟩ :=
      H.backwardSurvivorMap_crossing j.castSucc j.succ hle j le_rfl le_rfl x
    exact ⟨w, Subtype.ext ((E.oldTerminal_eq w).trans hw)⟩
  have hΨ : H.backwardSurvivorMap j.castSucc j.succ hle j.succ hle le_rfl = Subtype.val :=
    funext (H.backwardSurvivorMap_last j.castSucc j.succ hle)
  obtain ⟨d0, hd0, hb0⟩ := E.terminal.converges K hK 0 1 one_pos
  filter_upwards [E.terminal.eventually_scalar_close_on_compact hK hδ,
    Ioo_mem_nhdsLT hd0.2] with σ hσ hσd
  refine ⟨fun x => ?_, fun x z => ?_⟩
  · have hcr := H.backwardSurvivorMap_crossing j.castSucc j.succ hle j le_rfl le_rfl x
    have hΨx : H.backwardSurvivorMap j.castSucc j.succ hle j.succ hle le_rfl x = x.val :=
      H.backwardSurvivorMap_last j.castSucc j.succ hle x
    rw [hΨx] at hcr
    have hc : metricScalarAt E.terminal.metric (T x) =
        metricScalarAt (H.initialMetric j.succ) x.val := by
      rw [← H.event_output j]
      exact MetricCutCapEvent.RegularCrossing.scalar_eq E (p := T x) hcr
    rw [← hc]
    exact hσ (T x) (hTK x)
  · have hquad : ∀ (w : U) (v : TangentSpace ThreeModel w),
        ((E.incoming.flow.base.metric σ).restrictOpen E.incoming.terminalRegularOpen).inner (T w)
            (mfderiv ThreeModel ThreeModel T w v) (mfderiv ThreeModel ThreeModel T w v) ≤
          2 * ((H.initialMetric j.succ).restrictOpen U).inner w v v := by
      intro w v
      have hn := hb0 σ hσd (T w) (hTK w)
      have hb := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le E.terminal.metric
        ((E.incoming.flow.base.metric σ).restrictOpen E.incoming.terminalRegularOpen) (T w)
        hn.le (mfderiv ThreeModel ThreeModel T w v)).2
      have hm := H.backwardSurvivorMap_metric_crossing j.castSucc j.succ hle j le_rfl le_rfl w v v
      rw [hΨ, mfderiv_subtype_val_apply] at hm
      change _ ≤ 2 * (H.initialMetric j.succ).inner w.val v v
      rw [hm, show (2 : ℝ) = 1 + 1 by norm_num]
      exact hb
    have h1 := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
      ((H.initialMetric j.succ).restrictOpen U)
      ((E.incoming.flow.base.metric σ).restrictOpen E.incoming.terminalRegularOpen) T
      (H.backwardSurvivorTerminalMap_isLocalDiffeomorph j.castSucc j.succ hle j le_rfl le_rfl)
      two_pos hquad x z
    exact (riemannianEDistOf_le_restrictOpen (E.incoming.flow.base.metric σ)
      E.incoming.terminalRegularOpen (T x) (T z)).trans h1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
