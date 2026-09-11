import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Topology.Manifold.OpenTarget








noncomputable section

open Bundle Manifold DifferentialGeometry Set Filter ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]




theorem SmoothDiskExtension.exists_open_corestriction
    (N : TopologicalSpace.Opens M) {u : C(closedDisk, N)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(N, M)).comp u) U) :
    ∃ V : ℂ → N, SmoothDiskExtension (E := E) u V ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Subtype.val ∘ V) =ᶠ[𝓝 z] U := by
  classical
  obtain ⟨hval, S, hS, hDS, hU⟩ := h
  let V : ℂ → N := fun z => if hz : U z ∈ N then ⟨U z, hz⟩ else u (diskBoundary 0)
  let T := S ∩ U ⁻¹' (N : Set M)
  have hT : IsOpen T := hU.continuousOn.isOpen_inter_preimage hS N.isOpen
  have hDT : Metric.closedBall (0 : ℂ) 1 ⊆ T := by
    intro z hz
    refine ⟨hDS hz, ?_⟩
    change U z ∈ N
    rw [hval ⟨z, hz⟩]
    exact (u ⟨z, hz⟩).property
  have heq : EqOn (Subtype.val ∘ V) U T := by
    intro z hz
    dsimp only [Function.comp_apply, V]
    rw [dif_pos (show U z ∈ N from hz.2)]
  refine ⟨V, ⟨?_, T, hT, hDT, ?_⟩, ?_⟩
  · intro z
    apply Subtype.ext
    exact (heq (hDT z.property)).trans (hval z)
  · intro z hz
    apply (contMDiffWithinAt_subtypeVal_comp_iff N V T z).mp
    exact ((hU.mono inter_subset_left) z hz).congr heq (heq hz)
  · intro z hz
    exact Filter.eventuallyEq_of_mem (hT.mem_nhds (hDT hz)) heq

end DifferentialGeometry.Geometry
