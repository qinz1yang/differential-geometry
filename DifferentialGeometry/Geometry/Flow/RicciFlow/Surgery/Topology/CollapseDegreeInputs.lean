import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegree
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonLocalLength

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology
universe u

namespace DifferentialGeometry.Topology

theorem exists_eq_zsmul_pos_ne_zero_not_exists_linearMap_eq_one :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ 0 < k ∧ x ≠ 0 ∧
      ¬ ∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1 := by
  refine ⟨2, 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨φ, hφ⟩
  have h : φ 2 = 2 * φ 1 := by simpa using φ.map_smul (2 : ℤ) (1 : ℤ)
  rw [h] at hφ
  omega

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace GeometricCutoffRecord.ComparisonSupport

theorem localTerminalDistanceControl_const (K : G.ComparisonSupport c)
    (q : (G.Child c).Carrier) :
    K.LocalTerminalDistanceControl (ContinuousMap.const (G.Parent c).Carrier q) := by
  intro x hx
  refine ⟨{y : (G.Parent c).Carrier | y.1 ∈ (H.event i).incoming.terminalRegularRegion},
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage continuous_subtype_val).mem_nhds
      (K.support_terminal x hx), fun _ hy => hy, ?_⟩
  intro y _ z _ hy hz
  simp [ContinuousMap.const_apply, riemannianEDistOf_self]

theorem localTerminalDistanceControl_of_localTerminalEDistComparison
    (Kc : (c' : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c')
    (h : G.LocalTerminalEDistComparison Kc) :
    (Kc c).LocalTerminalDistanceControl (Kc c).canonicalWholeParentMap := by
  intro x hx
  obtain ⟨U, hU, hterm, hmain⟩ := h c x hx
  refine ⟨U, hU, hterm, fun y hy z hz hy' hz' => ?_⟩
  exact (riemannianEDistOf_le_restrictOpen (H.event i).outputMetric
      ((H.stage i.succ).componentOpen c) _ _).trans (hmain y hy z hz hy' hz')

end GeometricCutoffRecord.ComparisonSupport

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
