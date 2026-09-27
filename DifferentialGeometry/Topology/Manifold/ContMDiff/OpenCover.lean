import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
variable {E F G H H' H'' P M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {L : ModelWithCorners ℝ G H''}
  [TopologicalSpace P] [ChartedSpace H P]
  [TopologicalSpace M] [ChartedSpace H' M]
  [TopologicalSpace N] [ChartedSpace H'' N]

theorem contMDiffOn_of_open_cover_prod
    {ι : Type*} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    {A : Set P} {B : Set M} {f : P × M → N}
    (hf : ∀ i, ContMDiffOn (I.prod J) L ∞
      (fun p : P × U i => f (p.1, (p.2 : M))) (A ×ˢ (Subtype.val ⁻¹' B))) :
    ContMDiffOn (I.prod J) L ∞ f (A ×ˢ B) := by
  rintro ⟨t, x⟩ hp
  obtain ⟨i, hxi⟩ := hcover x
  let y : U i := ⟨x, hxi⟩
  let hloc := isLocalDiffeomorph_subtype_val (I := J) (U i) y
  let V : Set (P × M) := {p | p.2 ∈ hloc.localInverse.source}
  have hV : V ∈ 𝓝 (t, x) := continuous_snd.continuousAt.preimage_mem_nhds
    (hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source)
  let ψ : P × M → P × U i := fun p => (p.1, hloc.localInverse p.2)
  have hmap : ContMDiffAt (I.prod J) (I.prod J) ∞ ψ (t, x) :=
    contMDiffAt_fst.prodMk (hloc.localInverse_contMDiffAt.comp (t, x) contMDiffAt_snd)
  have hleft : hloc.localInverse x = y :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hg := hf i (ψ (t, x)) (show ψ (t, x) ∈ A ×ˢ (Subtype.val ⁻¹' B) by
    exact ⟨hp.1, by change (hloc.localInverse x : M) ∈ B; rw [hleft]; exact hp.2⟩)
  have hcomp := hg.comp (t, x) hmap.contMDiffWithinAt
    (show MapsTo ψ ((A ×ˢ B) ∩ V) (A ×ˢ (Subtype.val ⁻¹' B)) by
      intro p hp
      refine ⟨hp.1.1, ?_⟩
      change (hloc.localInverse p.2 : M) ∈ B
      rw [hloc.localInverse_right_inv hp.2]
      exact hp.1.2)
  have hsm := hcomp.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds hV))
  apply hsm.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hV] with p hp
    change f p = f (p.1, (hloc.localInverse p.2 : M))
    rw [hloc.localInverse_right_inv hp]
  · change f (t, x) = f (t, (hloc.localInverse x : M))
    rw [hleft]

end DifferentialGeometry
