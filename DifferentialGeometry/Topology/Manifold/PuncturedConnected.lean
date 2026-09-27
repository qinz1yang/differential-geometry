import DifferentialGeometry.Topology.PuncturedConnected
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

set_option autoImplicit false

open Filter Set
open scoped Topology

theorem ChartedSpace.isPathConnected_compl_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) (p : M) :
    IsPathConnected ({p}ᶜ : Set M) := by
  let _ : T1Space M := ChartedSpace.t1Space E M
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  let e : OpenPartialHomeomorph M E := chartAt E p
  have hp : p ∈ e.source := mem_chart_source E p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (e.open_target.mem_nhds (e.map_source hp))
  let U : Set M := e.symm '' Metric.ball (e p) r
  have hopen : IsOpen U := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
  have hpU : p ∈ U := ⟨e p, Metric.mem_ball_self hr, e.left_inv hp⟩
  have himage : e.symm '' (Metric.ball (e p) r \ {e p}) = U \ {p} := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
      intro heq
      apply hz.2
      exact (e.right_inv (hball hz.1)).symm.trans (congrArg e heq)
    · rintro y ⟨⟨z, hz, rfl⟩, hne⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      intro heq
      apply hne
      exact (congrArg e.symm heq).trans (e.left_inv hp)
  apply isPathConnected_compl_singleton_of_punctured_neighborhood p (hopen.mem_nhds hpU)
  rw [← himage]
  exact ((Metric.isPathConnected_ball_sdiff_singleton hdim (e p) hr).image'
    (e.continuousOn_symm.mono (fun z hz => hball hz.1))).isConnected


theorem ModelWithCorners.isPathConnected_compl_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) (p : M) :
    IsPathConnected ({p}ᶜ : Set M) := by
  let _ : ChartedSpace E H := I.toHomeomorph.symm.chartedSpace
  let _ : ChartedSpace E M := ChartedSpace.comp E H M
  exact ChartedSpace.isPathConnected_compl_singleton hdim p
