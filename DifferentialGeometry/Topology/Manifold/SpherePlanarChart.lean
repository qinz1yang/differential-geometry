import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
open Set Metric Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smooth_planar_chart_sphere
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ e : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ℂ,
      e.source = {v}ᶜ ∧ e.target = univ ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ e.symm e.target := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let s := stereographic' 2 v
  let L := Complex.orthonormalBasisOneI.repr.symm
  let e := s.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hs : s ∈ IsManifold.maximalAtlas (𝓡 2) ∞
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    IsManifold.subset_maximalAtlas ⟨v, rfl⟩
  have hss : e.source = s.source := by simp [e]
  have hst : s.target = univ := stereographic'_target v
  have het : e.target = univ := by simp [e, hst]
  refine ⟨e, hss.trans (stereographic'_source v), het, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ s.source := hss ▸ hx
    exact (L.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas hs hxs)).contMDiffWithinAt
  · intro z _
    have hsz : L.symm z ∈ s.target := hst ▸ mem_univ _
    exact ((contMDiffAt_symm_of_mem_maximalAtlas hs hsz).comp z
      L.symm.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffAt).contMDiffWithinAt

end DifferentialGeometry.Topology.Manifold
