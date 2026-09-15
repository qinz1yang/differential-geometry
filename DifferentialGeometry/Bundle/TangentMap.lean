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
