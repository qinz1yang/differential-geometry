import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import Mathlib.Geometry.Manifold.Immersion

open Set
open scoped ContDiff Manifold

namespace Manifold

variable {E F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M]

theorem isImmersionAtOfComplement_of_flat_patch
    (hn : n ≠ 0) (χ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M n)
    (Ψ : (E × F) ≃ₘ^n⟮𝓘(ℝ, E × F), 𝓘(ℝ, G)⟯ G) {g : M → G}
    (hflat : ∀ y ∈ χ.source, g (χ y) = Ψ (y, 0)) {x : E} (hx : x ∈ χ.source) :
    IsImmersionAtOfComplement F 𝓘(ℝ, E) 𝓘(ℝ, G) n g (χ x) := by
  let L : (E × F) ≃L[ℝ] G := Ψ.mfderivToContinuousLinearEquiv hn (x, 0)
  let A : (E × F) ≃ₘ^n⟮𝓘(ℝ, E × F), 𝓘(ℝ, G)⟯ G :=
    { toEquiv := L.toEquiv
      contMDiff_toFun := L.contDiff.contMDiff
      contMDiff_invFun := L.symm.contDiff.contMDiff }
  let C := Ψ.symm.trans A
  apply IsImmersionAtOfComplement.mk_of_charts L χ.symm.toOpenPartialHomeomorph
    C.toPartialDiffeomorph.toOpenPartialHomeomorph (χ.map_source hx) (mem_univ _)
    (DifferentialGeometry.PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas χ.symm)
    (DifferentialGeometry.PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas
      C.toPartialDiffeomorph)
  · exact fun _ _ => mem_univ _
  · intro y hy
    have hy' : y ∈ χ.source := by simpa using hy
    change L (Ψ.symm (g (χ y))) = L (y, 0)
    rw [hflat y hy', Ψ.symm_apply_apply]

end Manifold
