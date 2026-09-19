import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Bundle Manifold Set
open scoped Bundle Manifold Topology

namespace ContMDiffOn

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem continuousOn_mfderiv_apply {r : F → M} {U : Set F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U) (hU : IsOpen U) (v : G) :
    ContinuousOn (fun q : F × (G →L[ℝ] F) =>
      TotalSpace.mk' E (r q.1) (mfderiv 𝓘(ℝ, F) I r q.1 (q.2 v))) (Prod.fst ⁻¹' U) := by
  have ht := hr.continuousOn_tangentMapWithin le_rfl hU.uniqueMDiffOn
  have hv : Continuous (fun q : F × (G →L[ℝ] F) =>
      (TotalSpace.mk' F q.1 (q.2 v) : TangentBundle 𝓘(ℝ, F) F)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.clm_apply continuous_const))
  have hcomp := ht.comp hv.continuousOn (fun q hq => hq)
  apply hcomp.congr
  intro q hq
  dsimp only [Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hq)]

end ContMDiffOn

section

noncomputable section

open Function
open scoped ContDiff

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_source_tangentMapWithin {r : V → M} {U : Set V}
    {m n : WithTop ℕ∞} (hU : UniqueDiffOn ℝ U)
    (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n r U) (hmn : m + 1 ≤ n) :
    ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, V)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (fun p : V × V =>
        TotalSpace.mk' E (r p.1) (mfderivWithin 𝓘(ℝ, V) 𝓘(ℝ, E) r U p.1 p.2)) (U ×ˢ univ) := by
  have htr := hr.contMDiffOn_tangentMapWithin hmn hU.uniqueMDiffOn
  have hv : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, V)) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) m
      (fun p : V × V => (TotalSpace.mk' V p.1 p.2 : TangentBundle 𝓘(ℝ, V) V)) := by
    intro p
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_fst, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, V).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) m
        (fun q : V × V => q.2) p)
  exact htr.comp hv.contMDiffOn (fun p hp => hp.1)

theorem contMDiffOn_source_partialWithin {r : V → M} {U : Set V}
    {m n : WithTop ℕ∞} (hU : UniqueDiffOn ℝ U)
    (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) n r U) (hmn : m + 1 ≤ n) (v : V) :
    ContMDiffOn 𝓘(ℝ, V) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (fun z => TotalSpace.mk' E (r z) (mfderivWithin 𝓘(ℝ, V) 𝓘(ℝ, E) r U z v)) U :=
  (contMDiffOn_source_tangentMapWithin hU hr hmn).comp
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hz => ⟨hz, mem_univ _⟩)

end DifferentialGeometry.Geometry

end

end
