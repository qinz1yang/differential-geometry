import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseCoreFiber

attribute [local instance]
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreCharts
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.coreSmooth

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord.ComparisonSupport
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier} (K : G.ComparisonSupport c)

private theorem exists_isOpen_survivor_neighborhood (x : G.transition.ChildCore c)
    (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    ∃ U : Set (G.Parent c).Carrier, IsOpen U ∧
      G.transition.childCoreIntoParent c x ∈ U ∧
      ∀ y ∈ U, ∃ z : G.transition.ChildCore c,
        G.transition.childCoreIntoParent c z = y ∧
        K.rfs_whole_parent_map y = G.transition.childCoreInclusion c z := by
  obtain ⟨U, hU, hUopen, hxU⟩ := mem_nhds_iff.mp
    (G.transition.range_childCoreIntoParent_mem_nhds c x hx)
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  obtain ⟨z, hz⟩ := hU hy
  exact ⟨z, hz, hz ▸ K.rfs_whole_parent_map_childCore z⟩

theorem exists_smooth_survivor_lift (x : G.transition.ChildCore c)
    (hx : (𝓡∂ 3).IsInteriorPoint x.1) :
    letI : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
    ∃ U : TopologicalSpace.Opens (G.Parent c).Carrier,
      G.transition.childCoreIntoParent c x ∈ U ∧
      ∃ σ : U → (H.event i).old,
        ContMDiff ThreeModel (𝓡∂ 3) ∞ σ ∧
        (∀ y, (σ y).1.1 = y.1.1) ∧
        (∀ y, (H.event i).oldOutput (σ y) = (K.rfs_whole_parent_map y.1).1) := by
  classical
  let oldCharts : ChartedSpace (EuclideanHalfSpace 3) (H.event i).old := (H.event i).oldCharts
  let oldSmooth : IsManifold (𝓡∂ 3) ∞ (H.event i).old := (H.event i).oldSmooth
  obtain ⟨V, hVopen, hxV, hV⟩ := K.exists_isOpen_survivor_neighborhood x hx
  let U : TopologicalSpace.Opens (G.Parent c).Carrier := ⟨V, hVopen⟩
  choose z hz hzmap using fun y : U => hV y.1 y.2
  let σ : U → (H.event i).old := fun y =>
    ⟨(z y).1, childCore_subset_old (z y)⟩
  have hσval : ∀ y : U, (σ y).1.1 = y.1.1 := fun y => congrArg Subtype.val (hz y)
  have hσcomp : ((fun q : (H.event i).old => q.1.1) ∘ σ) =
      (fun y : U => y.1.1) := funext hσval
  have hσcont : Continuous σ :=
    (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).continuous_iff.mpr
      (by
        change Continuous ((fun q : (H.event i).old => q.1.1) ∘ σ)
        rw [hσcomp]
        exact continuous_subtype_val.comp continuous_subtype_val)
  have hσsmooth : ContMDiff ThreeModel (𝓡∂ 3) ∞ σ := by
    rw [ContMDiff.iff_comp_isImmersion (H.event i).old_induced.isImmersion]
    refine ⟨hσcont, ?_⟩
    rw [hσcomp]
    exact (contMDiff_subtype_val (U := (H.stage i.castSucc).componentOpen
      (G.transition.childParent c))).comp (contMDiff_subtype_val (U := U))
  refine ⟨U, hxV, σ, hσsmooth, hσval, ?_⟩
  intro y
  change (H.event i).oldOutput ⟨(z y).1, childCore_subset_old (z y)⟩ = _
  rw [oldOutput_eq_childCoreInclusion]
  exact congrArg Subtype.val (hzmap y).symm

end GeometricCutoffRecord.ComparisonSupport
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
