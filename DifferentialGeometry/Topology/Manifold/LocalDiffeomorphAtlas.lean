import DifferentialGeometry.Topology.Manifold.OpenCoverLocalDiffeomorph

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {ι E X F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ F H)
  (c : ι → OpenPartialHomeomorph X E)
  (hcover : ∀ x, ∃ i, x ∈ (c i).source) (f : X → M)

theorem isLocalDiffeomorph_chartedSpaceOfOpenCover
    (hlocal : ∀ i, IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞ (f ∘ (c i).symm) (c i).target) :
    let _ := chartedSpaceOfOpenCover c hcover
    IsManifold 𝓘(ℝ, E) ∞ X ∧ IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ f := by
  have hcompat (i j : ι) : ContDiffOn ℝ ∞ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source := by
    have h := (c i).symm.contMDiffOn_transition_of_localDiffeomorph (c j).symm f
      (hlocal i) (hlocal j)
    exact contMDiffOn_iff_contDiffOn.mp h
  let _ := chartedSpaceOfOpenCover c hcover
  let _ : IsManifold 𝓘(ℝ, E) ∞ X := isManifold_chartedSpaceOfOpenCover c hcover hcompat
  refine ⟨inferInstance, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  have hc : c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ X :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
      (show c i ∈ atlas E X from ⟨i, rfl⟩)
  let φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X E ∞ :=
    { (c i).toPartialEquiv with
      open_source := (c i).open_source
      open_target := (c i).open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hc
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hc }
  have hφ : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (c i).symm (c i x) :=
    φ.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ((c i).map_source hi)
  have h := DifferentialGeometry.isLocalDiffeomorphAt_of_comp
    (hlocal i ⟨c i x, (c i).map_source hi⟩) hφ
  rwa [(c i).left_inv hi] at h

end DifferentialGeometry.Topology.Manifold
