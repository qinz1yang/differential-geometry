import DifferentialGeometry.Geometry.Metric.SourceTangent



noncomputable section

open Set Function Bundle Manifold
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem contMDiffOn_source_tangentMap {r : V → M} {U : Set V}
    {m n : WithTop ℕ∞} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n r U) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, V)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (fun p : V × V =>
        TotalSpace.mk' E (r p.1) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r p.1 p.2)) (U ×ˢ univ) := by
  have htr := hr.contMDiffOn_tangentMapWithin hmn hU.uniqueMDiffOn
  have hv : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, V)) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) m
      (fun p : V × V => (TotalSpace.mk' V p.1 p.2 : TangentBundle 𝓘(ℝ, V) V)) := by
    intro p
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_fst, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, V).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) m
        (fun q : V × V => q.2) p)
  apply (htr.comp hv.contMDiffOn (fun p hp => hp.1)).congr
  intro p hp
  dsimp only [comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hp.1)]



theorem contMDiffOn_source_partial {r : V → M} {U : Set V}
    {m n : WithTop ℕ∞} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n r U) (hmn : m + 1 ≤ n) (v : V) :
    ContMDiffOn 𝓘(ℝ, V) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (fun z => TotalSpace.mk' E (r z) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r z v)) U :=
  (contMDiffOn_source_tangentMap hU hr hmn).comp
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hz => ⟨hz, mem_univ _⟩)

end DifferentialGeometry.Geometry
