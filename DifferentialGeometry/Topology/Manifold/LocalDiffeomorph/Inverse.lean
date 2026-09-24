import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Set
open scoped ContDiff Manifold

namespace Homeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}

theorem isLocalDiffeomorphAt_symm (h : M ≃ₜ N) {x : M}
    (hx : IsLocalDiffeomorphAt I J n h x) :
    IsLocalDiffeomorphAt J I n h.symm (h x) := by
  obtain ⟨e, hxe, he⟩ := hx
  refine ⟨e.symm, ?_, ?_⟩
  · change h x ∈ e.target
    rw [he hxe]
    exact e.map_source hxe
  · intro y hy
    apply h.injective
    rw [h.apply_symm_apply]
    have hy' : y ∈ e.target := hy
    exact ((he (e.map_target hy')).trans (e.right_inv hy')).symm

theorem isLocalDiffeomorphAt_symm_iff (h : M ≃ₜ N) {y : N} :
    IsLocalDiffeomorphAt J I n h.symm y ↔
      IsLocalDiffeomorphAt I J n h (h.symm y) := by
  constructor
  · intro hy
    exact h.symm.isLocalDiffeomorphAt_symm hy
  · intro hx
    simpa only [h.apply_symm_apply] using h.isLocalDiffeomorphAt_symm hx

end Homeomorph
