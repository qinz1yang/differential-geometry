import DifferentialGeometry.Topology.Homology.ManifoldFundamentalClass
import DifferentialGeometry.Topology.Homology.EuclideanLocalTop

noncomputable section

open CategoryTheory Module Set
open scoped Manifold

universe u

namespace DifferentialGeometry.Topology

private theorem exists_manifold_local_generator
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (p : M) :
    ∃ c : integralLocalHomology (finrank ℝ E) p,
      Function.Bijective (fun k : ℤ => k • c) := by
  obtain ⟨c, hc⟩ := exists_integralLocalHomology_generator (chartAt E p p)
  let e := (integralLocalHomologyChartIso (Y := E) (finrank ℝ E) p).toLinearEquiv
  refine ⟨e.symm c, ?_⟩
  simpa only [Function.comp_def, map_zsmul] using e.symm.bijective.comp hc

theorem exists_integralSingularHomology_generator_of_simplyConnected
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    [CompactSpace M] [SimplyConnectedSpace M] :
    ∃ a : integralSingularHomology (finrank ℝ E) M,
      Function.Bijective (fun k : ℤ => k • a) ∧
      ∀ x : M, Function.Bijective (fun k : ℤ =>
        k • integralAbsoluteToRelative (finrank ℝ E) ({x}ᶜ : Set M) a) := by
  let p := Classical.arbitrary M
  obtain ⟨c, hc⟩ := exists_manifold_local_generator (E := E) p
  let e := LinearEquiv.ofBijective
    (integralAbsoluteToRelative (finrank ℝ E) ({p}ᶜ : Set M))
    (integralAbsoluteToRelative_bijective_of_simplyConnected (E := E) p)
  have ha : Function.Bijective (fun k : ℤ => k • e.symm c) := by
    simpa only [Function.comp_def, map_zsmul] using e.symm.bijective.comp hc
  refine ⟨e.symm c, ha, ?_⟩
  intro x
  simpa only [Function.comp_def, map_zsmul] using
    (integralAbsoluteToRelative_bijective_of_simplyConnected (E := E) x).comp ha

end DifferentialGeometry.Topology
