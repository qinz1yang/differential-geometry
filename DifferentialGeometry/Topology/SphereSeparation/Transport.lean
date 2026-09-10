import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Topology.SphereSeparation.Defs

set_option autoImplicit false

namespace Poincare.Topology.SphereSeparation

open Set

namespace SphereSides

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set X}

noncomputable def image (d : SphereSides S) (h : X ≃ₜ Y) :
    SphereSides (h '' S) where
  compactSide := h '' d.compactSide
  endSide := h '' d.endSide
  isOpen_compactSide := h.isOpenMap d.compactSide d.isOpen_compactSide
  isOpen_endSide := h.isOpenMap d.endSide d.isOpen_endSide
  isConnected_compactSide := h.isConnected_image.mpr d.isConnected_compactSide
  isConnected_endSide := h.isConnected_image.mpr d.isConnected_endSide
  disjoint := by
    rw [Set.disjoint_left]
    intro y hyB hyE
    rcases hyB with ⟨x, hxB, rfl⟩
    rcases hyE with ⟨z, hzE, hzx⟩
    have hzx' : z = x := h.injective hzx
    exact Set.disjoint_left.1 d.disjoint hxB (hzx' ▸ hzE)
  union_eq_compl := by
    rw [← Set.image_union, d.union_eq_compl, h.image_compl]
  isCompact_closure_compactSide := by
    rw [← h.image_closure]
    exact h.isCompact_image.mpr d.isCompact_closure_compactSide
  not_isCompact_closure_endSide := by
    intro hc
    apply d.not_isCompact_closure_endSide
    rw [← h.image_closure] at hc
    exact h.isCompact_image.mp hc
  frontier_compactSide := by
    rw [← h.image_frontier, d.frontier_compactSide]
  frontier_endSide := by
    rw [← h.image_frontier, d.frontier_endSide]
  closure_compactSide := by
    rw [← h.image_closure, d.closure_compactSide, Set.image_union]
  closure_endSide := by
    rw [← h.image_closure, d.closure_endSide, Set.image_union]
  interior_closure_compactSide := by
    rw [← h.image_closure, ← h.image_interior, d.interior_closure_compactSide]

@[simp]
theorem image_compactSide (d : SphereSides S) (h : X ≃ₜ Y) :
    (d.image h).compactSide = h '' d.compactSide :=
  rfl

@[simp]
theorem image_endSide (d : SphereSides S) (h : X ≃ₜ Y) :
    (d.image h).endSide = h '' d.endSide :=
  rfl

end SphereSides

namespace SphereSides

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω} {S : Set M}

noncomputable def imageDiffeomorph (d : SphereSides S)
    (h : Diffeomorph I J M N n) : SphereSides (h '' S) :=
  d.image h.toHomeomorph

@[simp]
theorem imageDiffeomorph_compactSide (d : SphereSides S)
    (h : Diffeomorph I J M N n) :
    (d.imageDiffeomorph h).compactSide = h '' d.compactSide :=
  rfl

@[simp]
theorem imageDiffeomorph_endSide (d : SphereSides S)
    (h : Diffeomorph I J M N n) :
    (d.imageDiffeomorph h).endSide = h '' d.endSide :=
  rfl

end SphereSides

end Poincare.Topology.SphereSeparation
