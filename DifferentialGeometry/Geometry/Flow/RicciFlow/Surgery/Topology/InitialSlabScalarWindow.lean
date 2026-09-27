import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabStartDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_forall_Icc_scalar_le_at_initial_slab_start (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ H : ObservedHistory.{u}, InitialIdentification P₀ g₀ H →
      ∀ {s : ℝ} (G : (H.stage 0).IncomingSlab (H.time 0) s),
      G.flow.base.metric (H.time 0) = H.initialMetric 0 →
      ∃ η : ℝ, 0 < η ∧ H.time 0 + η < s ∧
        ∀ t ∈ Icc (H.time 0) (H.time 0 + η), ∀ y : (H.stage 0).Carrier,
          G.flow.scalar t y ≤ Q₀ + 1 := by
  obtain ⟨Q₀, hQ₀, hstart⟩ := exists_scalar_lt_at_initial_slab_start.{u} P₀ g₀
  refine ⟨Q₀, hQ₀, fun H hH s G hG => ?_⟩
  obtain ⟨δ, hδ, hs, hc⟩ :=
    G.exists_forall_Icc_scalar_riemannNorm_metric_close ⟨le_rfl, G.lt⟩ one_pos
  refine ⟨δ, hδ, hs, fun t ht y => ?_⟩
  have hclose := (hc t ⟨(max_le le_rfl (by linarith)).trans ht.1, ht.2⟩ (H.time 0)
    ⟨max_le le_rfl (by linarith), by linarith⟩ y).1
  have hlt := hstart H hH G hG y
  linarith [(abs_le.mp hclose).2]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
