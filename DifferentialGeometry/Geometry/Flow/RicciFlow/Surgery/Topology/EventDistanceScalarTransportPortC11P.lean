import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalarPresentation

/-!
# EventDistanceScalarTransport (port, S-CH11-PORT-B1)

Source: donor `EventDistanceScalarTransport.lean` (chapter11 HEAD a73e4bdbfd), verbatim except for
the elaboration-level patch below. 来源：donor 原文，仅做 elaboration 层面修补。

Patches:
* donor L32 / port L46: `simpa only [hi] using hE` replaced by `rw [hi] at hE` then `exact hE`
  (simp does not rewrite the dependent stage/time arguments of `SamePresentation`; `rw`
  abstracts all occurrences at once).

No statement/definition/proof idea altered. 声明名、陈述、证明思路均未改动。
-/

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Preserve the certificate at the actual old event index in a longer history.
This is the lower-level form of the existing event_samePresentation_of_prefix
argument; that presentation has direction J to H, so its symmetry is used. -/
theorem ObservedHistory.IsPrefixOf.hasUniformDistanceScalar_event
    {H J : ObservedHistory.{u}} {C : ℝ≥0}
    (hp : H.IsPrefixOf J) (hn : H.eventCount ≤ J.eventCount)
    (i : Fin H.eventCount) (h : (H.event i).HasUniformDistanceScalar C) :
    (J.event (i.castLE hn)).HasUniformDistanceScalar C := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let iR : Fin (J.restrict a).eventCount := Fin.cast hp.presentation.count_eq.symm i
  have hi : Fin.cast hp.presentation.count_eq iR = i := Fin.ext rfl
  have hE := hp.presentation.event_eq iR
  change (J.event (i.castLE hn)).SamePresentation
    (H.event (Fin.cast hp.presentation.count_eq iR)) at hE
  have hpresent : (J.event (i.castLE hn)).SamePresentation (H.event i) := by
    rw [hi] at hE
    exact hE
  exact hpresent.symm.hasUniformDistanceScalar h

/-- A horizon restriction retains each selected event and its physical scalar
certificate; its possibly new final slab does not enter the assertion. -/
theorem RetainedCoreHistory.hasUniformDistanceScalar_restrict
    (H : RetainedCoreHistory.{u}) (t : Icc (0 : ℝ) H.horizon) {C : ℝ≥0}
    (h : ∀ i : Fin H.eventCount, (H.toHistory.event i).HasUniformDistanceScalar C) :
    ∀ i : Fin (H.restrict t).eventCount,
      ((H.restrict t).toHistory.event i).HasUniformDistanceScalar C := by
  intro i
  exact h (i.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage t).isLt))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
