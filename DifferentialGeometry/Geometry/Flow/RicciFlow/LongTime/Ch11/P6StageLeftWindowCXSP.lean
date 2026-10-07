import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalDistanceUpperLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

/-!
# CX-SPINE G8: a strict left window inside the current stage

The actual `closedPrefixAt` has an endpoint terminal limit metric whose distance
equals the original endpoint distance. Its restricted incoming slab has terminal
regular region `univ`. Apply the genuine terminal distance upper-limit theorem
with a strict ENNReal margin; no regularity beyond the closed endpoint is used.

Sources: `SlabTerminalConvergence.lean:115–144,181–191` and
`TerminalDistanceUpperLimit.lean:48–118`. Their SHA-256 hashes are respectively
`cea86a54361acc153793534f1f646f9916f3512c781c9607aadc99a9bb6a9f94` and
`ddc4749f54e344893e0a81d0a38bb058368a66f409312f4236c49cdf236ec1ac`.
This is a left neighborhood within the same stage, not an extension across its birth.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- A strict distance bound at a positive-age stage point persists on a whole
left interval in that same stage, including when the observation is the horizon. -/
theorem ObservedHistory.exists_stage_left_window_CXSP
    (H : ObservedHistory.{u}) (v : Icc (0 : ℝ) H.horizon)
    (hage : H.time (H.activeStage v) < (v : ℝ))
    (p q : (H.stageAt v).Carrier) {X : ℝ≥0∞}
    (hX : riemannianEDistOf (H.stageMetric (H.activeStage v) v) p q < X) :
    ∃ d ∈ Ico (H.time (H.activeStage v)) (v : ℝ), ∀ u ∈ Ioo d (v : ℝ),
      riemannianEDistOf (H.stageMetric (H.activeStage v) u) p q < X := by
  let A := H.closedPrefixAt v hage
  let G := A.restrictIncoming le_rfl A.lt le_rfl
  let L := A.endpointTerminalLimitMetric (H.stageAt v)
  have hmem (x : (H.stageAt v).Carrier) : x ∈ G.terminalRegularOpen := by
    change x ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
    rw [A.terminalRegularRegion_eq_univ (H.stageAt v)]
    exact mem_univ x
  let p' : G.terminalRegularOpen := ⟨p, hmem p⟩
  let q' : G.terminalRegularOpen := ⟨q, hmem q⟩
  have hclosedMetric (u : ℝ) :
      A.flow.base.metric u = H.stageMetric (H.activeStage v) u :=
    H.closedPrefixAt_metric v hage u
  have hmetric (u : ℝ) :
      G.flow.base.metric u = H.stageMetric (H.activeStage v) u := by
    change A.flow.base.metric u = _
    exact hclosedMetric u
  have hdist : riemannianEDistOf L.metric p' q' =
      riemannianEDistOf (H.stageMetric (H.activeStage v) v) p q := by
    change riemannianEDistOf (A.endpointTerminalLimitMetric (H.stageAt v)).metric p' q' = _
    rw [A.riemannianEDistOf_endpointTerminalLimitMetric, hclosedMetric]
  have hlimit : riemannianEDistOf L.metric p' q' < X := by rw [hdist]; exact hX
  obtain ⟨η, hη, hmargin⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hlimit
  have hηreal : 0 < (η : ℝ) := by exact_mod_cast hη
  obtain ⟨d, hd, hnear⟩ :=
    OrientedThreeStage.IncomingSlab.TerminalLimitMetric.eventually_ambient_edist_le
      G L p' q' (ne_top_of_lt hlimit) (η : ℝ) hηreal
  refine ⟨d, hd, ?_⟩
  intro u hu
  have hbound := hnear u hu
  rw [hmetric] at hbound
  exact hbound.trans_lt (by simpa only [ENNReal.ofReal_coe_nnreal] using hmargin)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
