import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem isTracedRegion.recenter {H : ObservedHistory.{u}}
    {t : Icc (0 : ℝ) H.horizon} {p q : (H.stageAt t).Carrier} {ρ τ K r : ℝ}
    (h : H.isTracedRegion t p ρ τ K) (hr : 0 < r)
    (hbuffer : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q +
      ENNReal.ofReal r ≤ ENNReal.ofReal ρ) :
    H.isTracedRegion t q r τ K := by
  obtain ⟨_, hτ, a, hat, ha, htrace⟩ := h
  refine ⟨hr, hτ, a, hat, ha, fun x hx => htrace x ?_⟩
  have hdist : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((le_add_right le_rfl).trans hbuffer)
  exact (riemannianEDistOf_triangle (H.stageMetric (H.activeStage t) t) p q x).trans_lt
    ((ENNReal.add_lt_add_left hdist hx).trans_le hbuffer)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
