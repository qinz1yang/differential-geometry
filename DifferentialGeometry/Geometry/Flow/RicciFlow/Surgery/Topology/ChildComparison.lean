import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildLengthComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseFundamentalClass

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
    (G : GeometricCutoffRecord H i parameters)

namespace ComparisonSupport

variable {G} {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

theorem rfs_collapse_degree :
    K.LocalTerminalLengthControl K.canonicalWholeParentMap ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.canonicalWholeParentMap y = K.canonicalWholeParentMap x) ∧
    (∀ x : G.transition.ChildCore c,
      K.canonicalWholeParentMap (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.canonicalWholeParentMap (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation ∧
    Function.Surjective K.canonicalWholeParentMap := by
  exact ⟨K.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl
    (rfs_whole_parent_map_localTerminalDistanceControl G K),
    fun _ hx => K.rfs_whole_parent_map_locallyConstant_of_notMem hx,
    K.rfs_whole_parent_map_childCore, K.rfs_whole_parent_map_fundamentalClass,
    K.rfs_whole_parent_map_surjective_of_cover K.rfs_collapse_cover⟩


end ComparisonSupport

theorem rfs_child_comparison
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
    (∀ c, ∃ K : G.ComparisonSupport c, f c = K.canonicalWholeParentMap) ∧
    (∀ c, integralHomologyMap 3 (f c) (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation) ∧
    ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  let Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c :=
    fun c => by
      letI := hSC (G.transition.childParent c)
      exact Classical.choice (G.rfs_comparison_support c)
  exact G.rfs_child_comparison_of_local_length_comparison Kc
    (fun c => (Kc c).rfs_whole_parent_map_fundamentalClass)
    (G.local_length_comparison Kc)


end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
