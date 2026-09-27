import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpaceExtension
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open Set Filter
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {X E M : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiffOn_extension_across_halfSpace_boundary
    {f : X × ℝ → M} {U : Set (X × ℝ)} {p : X}
    (hU : IsOpen U) (hp : (p, (0 : ℝ)) ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, X × ℝ) I ∞ f (U ∩ (univ ×ˢ Ici (0 : ℝ)))) :
    ∃ V : Set (X × ℝ), IsOpen V ∧ (p, (0 : ℝ)) ∈ V ∧ V ⊆ U ∧
      ∃ g : X × ℝ → M, ContMDiffOn 𝓘(ℝ, X × ℝ) I ∞ g V ∧
        EqOn g f (V ∩ (univ ×ˢ Ici (0 : ℝ))) := by
  let e : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I (f (p, 0))
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _ }
  have hpe : f (p, 0) ∈ e.source := mem_extChartAt_source _
  have he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source := by
    change ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I (f (p, 0)))
      (extChartAt I (f (p, 0))).source
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt (I := I) (n := ∞) (x := f (p, 0))
  have hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target :=
    contMDiffOn_extChartAt_symm (I := I) (f (p, 0))
  obtain ⟨W, hW, hpW, hWf⟩ := mem_nhdsWithin.mp
    ((hf.continuousOn (p, 0) ⟨hp, mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hpe))
  let A := U ∩ W
  have hAf : MapsTo f (A ∩ (univ ×ˢ Ici (0 : ℝ))) e.source := by
    intro x hx
    exact hWf ⟨hx.1.2, hx.1.1, hx.2⟩
  have hfc : ContDiffOn ℝ ∞ (e ∘ f) (A ∩ (univ ×ˢ Ici (0 : ℝ))) :=
    (he.comp (hf.mono (inter_subset_inter_left _ inter_subset_left)) hAf).contDiffOn
  obtain ⟨V, hV, hpV, hVA, g, hg, heq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_halfSpace_boundary
      (hU.inter hW) ⟨hp, hpW⟩ hfc
  have hgp : g (p, 0) = e (f (p, 0)) := heq ⟨hpV, mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩
  let N := V ∩ g ⁻¹' e.target
  have hN : IsOpen N := hg.continuousOn.isOpen_inter_preimage hV e.open_target
  have hpN : (p, (0 : ℝ)) ∈ N := by
    refine ⟨hpV, ?_⟩
    change g (p, 0) ∈ e.target
    rw [hgp]
    exact e.map_source hpe
  refine ⟨N, hN, hpN, (inter_subset_left.trans hVA).trans inter_subset_left,
    e.symm ∘ g, hei.comp (hg.mono inter_subset_left).contMDiffOn (fun x hx => hx.2), ?_⟩
  intro x hx
  change e.symm (g x) = f x
  rw [heq ⟨hx.1.1, hx.2⟩]
  exact e.left_inv (hAf ⟨hVA hx.1.1, hx.2⟩)

end DifferentialGeometry.Topology
