import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

noncomputable section
open Set Metric Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

theorem exists_smooth_punctured_sphere_chart (n : ℕ)
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ e : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (EuclideanSpace ℝ (Fin n)) ∞,
      e.source = {v}ᶜ ∧ e.target = univ := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let s := stereographic' n v
  have hs : s ∈ IsManifold.maximalAtlas (𝓡 n) ∞
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    IsManifold.subset_maximalAtlas ⟨v, rfl⟩
  let e : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (EuclideanSpace ℝ (Fin n)) ∞ :=
    { toPartialEquiv := s.toPartialEquiv
      open_source := s.open_source
      open_target := s.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hs
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hs }
  exact ⟨e, stereographic'_source v, stereographic'_target v⟩

end Poincare.Topology.Manifold
