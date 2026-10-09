import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
namespace DescendantInterior

private theorem connected_of_dense_local_inter {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {U : Set X} (hU : Dense U) (hne : U.Nonempty)
    (hloc : ∀ p : X, ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ IsPreconnected (V ∩ U)) :
    IsConnected U := by
  obtain ⟨x, hx⟩ := hne
  let C := connectedComponentIn U x
  have hCU : C ⊆ U := connectedComponentIn_subset U x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCo : IsOpen (closure C) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨V, hVo, hyV, hVU⟩ := hloc y
    obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.mp hy V hVo hyV
    have hVC : V ∩ U ⊆ C := by
      have hz : V ∩ U ⊆ connectedComponentIn U z :=
        hVU.subset_connectedComponentIn ⟨hzV, hCU hzC⟩ inter_subset_right
      rwa [← connectedComponentIn_eq hzC] at hz
    exact mem_of_superset (hVo.mem_nhds hyV)
      ((hU.open_subset_closure_inter hVo).trans (closure_mono hVC))
  have hCall : closure C = univ :=
    (show IsClopen (closure C) from ⟨isClosed_closure, hCo⟩).eq_univ
      ⟨x, subset_closure hxC⟩
  have hclosed : IsClosed ((Subtype.val : U → X) ⁻¹' C) := by
    simp only [C, connectedComponentIn_eq_image hx,
      Set.preimage_image_eq _ Subtype.val_injective]
    exact isClosed_connectedComponent
  have hUC : U ⊆ C := by
    have hh := isClosed_preimage_val.mp hclosed
    simpa only [inter_eq_right.mpr hCU, hCall, inter_univ] using hh
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [← subset_antisymm hCU hUC]
  exact isPreconnected_connectedComponentIn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chart_inverse_interior (p : M) {v : E}
    (hv : v ∈ interior (extChartAt I p).target) :
    (extChartAt I p).symm v ∈ I.interior M := by
  have hvt : v ∈ (extChartAt I p).target := interior_subset hv
  have hy : (extChartAt I p).symm v ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using (extChartAt I p).map_target hvt
  apply (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H p) hy).mpr
  change (extChartAt I p) ((extChartAt I p).symm v) ∈ interior (extChartAt I p).target
  simpa only [(extChartAt I p).right_inv hvt] using hv

private theorem dense_interior : Dense (I.interior M) := by
  intro p
  have hc : extChartAt I p p ∈ closure (interior (extChartAt I p).target) :=
    extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) p)
  have him := mem_closure_image
    ((chartAt H p).continuousAt_extend_symm (I := I) (mem_chart_source H p)) hc
  have hsub : (extChartAt I p).symm '' interior (extChartAt I p).target ⊆ I.interior M := by
    rintro _ ⟨v, hv, rfl⟩
    exact chart_inverse_interior I p hv
  have hh := closure_mono hsub him
  change (extChartAt I p).symm (extChartAt I p p) ∈ closure (I.interior M) at hh
  rw [(extChartAt I p).left_inv (mem_extChartAt_source p)] at hh
  exact hh

private theorem locally_preconnected_inter_interior (p : M) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ IsPreconnected (V ∩ I.interior M) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (extChartAt_target_union_compl_range_mem_nhds_of_mem (mem_extChartAt_target (I := I) p))
  have hsub : Metric.ball (extChartAt I p p) r ∩ range I ⊆ (extChartAt I p).target := by
    intro v hv
    rcases hball hv.1 with h | h
    · exact h
    · exact False.elim (h hv.2)
  let V : Set M := (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) r
  have hVo : IsOpen V := (chartAt H p).isOpen_extend_preimage' Metric.isOpen_ball
  have hpV : p ∈ V := ⟨mem_extChartAt_source p, Metric.mem_ball_self hr⟩
  refine ⟨V, hVo, hpV, ?_⟩
  have he : V ∩ I.interior M =
      (extChartAt I p).symm '' (Metric.ball (extChartAt I p p) r ∩ interior (range I)) := by
    ext y
    constructor
    · rintro ⟨⟨hyS, hyB⟩, hyI⟩
      have hyChart : extChartAt I p y ∈ interior (extChartAt I p).target := by
        apply (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
          (chart_mem_atlas H p) ?_).mp hyI
        simpa only [extChartAt_source] using hyS
      refine ⟨extChartAt I p y, ⟨hyB, ?_⟩, (extChartAt I p).left_inv hyS⟩
      exact interior_mono (extChartAt_target_subset_range p) hyChart
    · rintro ⟨v, hv, rfl⟩
      have hvt := hsub ⟨hv.1, interior_subset hv.2⟩
      have hvi : v ∈ interior (extChartAt I p).target :=
        (extChartAt_target_eventuallyEqSet_of_mem hvt).symm.mem_interior hv.2
      refine ⟨⟨(extChartAt I p).map_target hvt, ?_⟩, chart_inverse_interior I p hvi⟩
      simpa only [mem_preimage, (extChartAt I p).right_inv hvt] using hv.1
  rw [he]
  apply ((convex_ball (extChartAt I p p) r).inter I.convex_range.interior).isPreconnected.image
  exact (continuousOn_extChartAt_symm p).mono (fun _ hv => hsub ⟨hv.1, interior_subset hv.2⟩)

private theorem connected_native_interior [ConnectedSpace M] : IsConnected (I.interior M) := by
  have hne : (I.interior M).Nonempty := by
    obtain ⟨p⟩ := (inferInstance : Nonempty M)
    obtain ⟨v, hv⟩ := interior_extChartAt_target_nonempty I p
    exact ⟨_, chart_inverse_interior I p hv⟩
  exact connected_of_dense_local_inter (dense_interior I) hne (locally_preconnected_inter_interior I)
end DescendantInterior

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)


theorem childCore_nonempty (c : ConnectedComponents Q.Carrier) : Nonempty (E.ChildCore c) := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  exact ⟨⟨x, hx⟩⟩


theorem childCore_compact (c : ConnectedComponents Q.Carrier) : CompactSpace (E.ChildCore c) := by
  let := E.core_compact
  apply isCompact_iff_compactSpace.mp
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  have he : {y : E.trace.tubes.core | ConnectedComponents.mk y = E.childCoreComponent c} =
      connectedComponent x := by
    ext y
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe'
  change IsCompact {y : E.trace.tubes.core | ConnectedComponents.mk y = E.childCoreComponent c}
  rw [he]
  exact isClosed_connectedComponent.isCompact


theorem childCore_connected (c : ConnectedComponents Q.Carrier) : ConnectedSpace (E.ChildCore c) := by
  apply isConnected_iff_connectedSpace.mp
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  have he : {y : E.trace.tubes.core | ConnectedComponents.mk y = E.childCoreComponent c} =
      connectedComponent x := by
    ext y
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe'
  change IsConnected {y : E.trace.tubes.core | ConnectedComponents.mk y = E.childCoreComponent c}
  rw [he]
  exact isConnected_connectedComponent

theorem childCore_isOpen (c : ConnectedComponents Q.Carrier) :
    IsOpen {x : E.trace.tubes.core | ConnectedComponents.mk x = E.childCoreComponent c} := by
  let := E.core_locallyConnected
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  have he : {y : E.trace.tubes.core | ConnectedComponents.mk y = E.childCoreComponent c} =
      connectedComponent x := by
    ext y
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe'
  rw [he]
  exact isOpen_connectedComponent


def childCoreOpen (c : ConnectedComponents Q.Carrier) : TopologicalSpace.Opens E.trace.tubes.core :=
  ⟨{x | ConnectedComponents.mk x = E.childCoreComponent c}, E.childCore_isOpen c⟩

@[instance_reducible] def childCoreCharts (c : ConnectedComponents Q.Carrier) :
    ChartedSpace (EuclideanHalfSpace 3) (E.ChildCore c) :=
  let := E.coreCharts
  inferInstanceAs (ChartedSpace (EuclideanHalfSpace 3) (E.childCoreOpen c))


theorem childCore_isManifold (c : ConnectedComponents Q.Carrier) :
    let := E.childCoreCharts c
    IsManifold (𝓡∂ 3) ∞ (E.ChildCore c) := by
  let := E.coreCharts
  let := E.coreSmooth
  exact inferInstanceAs (IsManifold (𝓡∂ 3) ∞ (E.childCoreOpen c))

theorem childCore_boundary (c : ConnectedComponents Q.Carrier) :
    let := E.coreCharts
    let := E.childCoreCharts c
    (𝓡∂ 3).boundary (E.ChildCore c) =
      (Subtype.val : E.ChildCore c → E.trace.tubes.core) ⁻¹' (𝓡∂ 3).boundary E.trace.tubes.core := by
  let := E.coreCharts
  exact (𝓡∂ 3).boundary_open (u := E.childCoreOpen c)

theorem childCore_interior_nonempty (c : ConnectedComponents Q.Carrier) :
    let := E.childCoreCharts c
    ((𝓡∂ 3).interior (E.ChildCore c)).Nonempty := by
  let := E.childCoreCharts c
  let := E.childCore_isManifold c
  let := E.childCore_nonempty c
  obtain ⟨x⟩ := (inferInstance : Nonempty (E.ChildCore c))
  obtain ⟨v, hv⟩ := interior_extChartAt_target_nonempty (𝓡∂ 3) x
  have hvt : v ∈ (extChartAt (𝓡∂ 3) x).target := interior_subset hv
  let y := (extChartAt (𝓡∂ 3) x).symm v
  have hy : y ∈ (chartAt (EuclideanHalfSpace 3) x).source := by
    simpa only [extChartAt_source] using (extChartAt (𝓡∂ 3) x).map_target hvt
  refine ⟨y, ?_⟩
  apply ((𝓡∂ 3).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas (EuclideanHalfSpace 3) x) hy).mpr
  change (extChartAt (𝓡∂ 3) x) y ∈ interior (extChartAt (𝓡∂ 3) x).target
  simpa only [y, (extChartAt (𝓡∂ 3) x).right_inv hvt] using hv

theorem childCore_interior_connected (c : ConnectedComponents Q.Carrier) :
    let := E.childCoreCharts c
    IsConnected ((𝓡∂ 3).interior (E.ChildCore c)) := by
  let := E.childCoreCharts c
  let := E.childCore_isManifold c
  let := E.childCore_connected c
  exact DescendantInterior.connected_native_interior (𝓡∂ 3)

theorem childParent_unique (c : ConnectedComponents Q.Carrier) :
    ∃! parent : ConnectedComponents P.Carrier,
      ∀ x : E.ChildCore c, ConnectedComponents.mk x.1.1 = parent := by
  refine ⟨E.childParent c, E.childCore_mem_parent c, ?_⟩
  intro parent hp
  obtain ⟨x⟩ := E.childCore_nonempty c
  exact (hp x).symm.trans (E.childCore_mem_parent c x)

theorem rfs_actual_descendants (c : ConnectedComponents Q.Carrier) :
    let := E.childCoreCharts c
    Nonempty (E.ChildCore c) ∧ CompactSpace (E.ChildCore c) ∧ ConnectedSpace (E.ChildCore c) ∧
      IsManifold (𝓡∂ 3) ∞ (E.ChildCore c) ∧
      IsConnected ((𝓡∂ 3).interior (E.ChildCore c)) :=
  ⟨E.childCore_nonempty c, E.childCore_compact c, E.childCore_connected c,
    E.childCore_isManifold c, E.childCore_interior_connected c⟩

end SmoothCutCapTransition
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
