import DifferentialGeometry.Topology.Homology.RelativeCapToAbsoluteHomology
import DifferentialGeometry.Topology.Homology.CochainExcision
import DifferentialGeometry.Topology.Homology.LocalCharts
import DifferentialGeometry.Topology.Homology.NormedLocalCapDuality

noncomputable section

open CategoryTheory Module Set

universe u

namespace DifferentialGeometry.Topology

theorem integralManifoldLocalHomology_cap_bijective_of_generator
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [PreconnectedSpace M]
    (x : M) (c : integralLocalHomology (finrank ℝ E) x)
    (hc : Function.Bijective (fun z : ℤ => z • c)) :
    Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E) ({x}ᶜ : Set M) =>
      integralRelativeCohomologyCapToAbsolute ({x}ᶜ : Set M) (finrank ℝ E) 0 α c) := by
  let _ : T1Space M := ChartedSpace.t1Space E M
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  let _ : ConnectedSpace M :=
    { toPreconnectedSpace := inferInstance
      toNonempty := ⟨x⟩ }
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let e := chartAt E x
  let U := pathComponentIn e.source x
  have hx : x ∈ e.source := mem_chart_source E x
  have hU : IsOpen U := e.open_source.pathComponentIn x
  have hxU : x ∈ U := mem_pathComponentIn_self hx
  have hUs : U ⊆ e.source := pathComponentIn_subset
  let _ : PathConnectedSpace U :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_pathComponentIn hx)
  let V := e '' U
  have hV : IsOpen V := e.isOpen_image_of_subset_source hU hUs
  let h : U ≃ₜ V := e.homeomorphOfImageSubsetSource hUs rfl
  let _ : PathConnectedSpace V := h.surjective.pathConnectedSpace h.continuous
  let p : U := ⟨x, hxU⟩
  let q : V := h p
  let jU := (integralLocalHomologyNeighborhoodIso (finrank ℝ E) x U hU hxU).toLinearEquiv
  let cU := jU.symm c
  have hcU : Function.Bijective (fun z : ℤ => z • cU) := by
    simpa only [Function.comp_def, map_zsmul] using jU.symm.bijective.comp hc
  let jH := (integralLocalHomologyHomeomorphIso (finrank ℝ E) h p).toLinearEquiv
  let cV := jH cU
  have hcV : Function.Bijective (fun z : ℤ => z • cV) := by
    simpa only [Function.comp_def, map_zsmul] using jH.bijective.comp hcU
  let jV := (integralLocalHomologyNeighborhoodIso (finrank ℝ E) (q : E)
    V hV q.property).toLinearEquiv
  let cE := jV cV
  have hcE : Function.Bijective (fun z : ℤ => z • cE) := by
    simpa only [Function.comp_def, map_zsmul] using jV.bijective.comp hcV
  have hcapE := integralLocalHomology_cap_bijective_of_generator (q : E) cE hcE
  have hcapV := (integralRelativeCohomologyCapToAbsolute_bijective_map_iff
    (finrank ℝ E) 0 (singularSubspaceInclusion V)
    (neighborhoodPointComplement_mapsTo (q : E) V q.property)
    (integralSingularHomologyZeroMapEquiv (singularSubspaceInclusion V)).bijective
    (integralRelativeCohomologyMap_point_neighborhood_bijective
      (finrank ℝ E) (q : E) V hV q.property) cV).mp hcapE
  let f : ContinuousMap U V := ⟨h, h.continuous⟩
  have hf : MapsTo f ({p}ᶜ : Set U) ({q}ᶜ : Set V) :=
    fun _ hy => h.injective.ne hy
  let g := h.subtype (p := fun a : U => a ∈ ({p}ᶜ : Set U))
    (q := fun b : V => b ∈ ({q}ᶜ : Set V)) (fun a => h.injective.ne_iff.symm)
  have hcoh : Function.Bijective (integralRelativeCohomologyMap (finrank ℝ E) f hf) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv h.toHomotopyEquiv n
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv g.toHomotopyEquiv n
  have hcapU := (integralRelativeCohomologyCapToAbsolute_bijective_map_iff
    (finrank ℝ E) 0 f hf (integralSingularHomologyZeroMapEquiv f).bijective hcoh cU).mp hcapV
  have hout := integralRelativeCohomologyCapToAbsolute_bijective_map
    (finrank ℝ E) 0 (singularSubspaceInclusion U)
    (neighborhoodPointComplement_mapsTo x U hxU)
    (integralSingularHomologyZeroMapEquiv (singularSubspaceInclusion U)).bijective
    (integralRelativeCohomologyMap_point_neighborhood_bijective
      (finrank ℝ E) x U hU hxU) cU hcapU
  change Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E) ({x}ᶜ : Set M) =>
    integralRelativeCohomologyCapToAbsolute ({x}ᶜ : Set M) (finrank ℝ E) 0 α
      (jU (jU.symm c))) at hout
  rwa [jU.apply_symm_apply] at hout

end DifferentialGeometry.Topology

end
