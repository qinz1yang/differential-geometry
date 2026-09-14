import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeInputs

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology
universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace GeometricCutoffRecord

namespace ComparisonSupport

theorem rfs_collapse_degree_of_localTerminalEDistComparison
    (Kc : (c' : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c')
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ} (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hmap : integralHomologyMap 3 (Kc c).rfs_whole_parent_map a = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map a) = 1)
    (hk : 0 < k) :
    (Kc c).LocalTerminalLengthControl (Kc c).rfs_whole_parent_map ∧
    (∀ x ∉ (Kc c).support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      (Kc c).rfs_whole_parent_map y = (Kc c).rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      (Kc c).rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 (Kc c).rfs_whole_parent_map a = b ∧
    Function.Surjective (Kc c).rfs_whole_parent_map :=
  (Kc c).rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator a b
    (localTerminalDistanceControl_of_localTerminalEDistComparison Kc hcollapse) hmap hgen hk

end ComparisonSupport

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
