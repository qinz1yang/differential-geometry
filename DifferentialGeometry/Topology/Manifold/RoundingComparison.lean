import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Inverse
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

open Set
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}

theorem isLocalDiffeomorph_unrounding
    (c : PartialDiffeomorph I J M N n) (R₀ : M ≃ₜ M) (R₁ : N ≃ₜ N)
    (Q : Diffeomorph I J M N n) {K : Set M} {L : Set N}
    (hR₀ : ∀ x ∉ K, IsLocalDiffeomorphAt I I n R₀ x)
    (hR₁ : ∀ y ∉ L, IsLocalDiffeomorphAt J J n R₁ y)
    (hcKL : c '' K = L) {U : Set M} (hU : IsOpen U) (hKU : K ⊆ U)
    (hUc : U ⊆ c.source) (hcomm : ∀ x ∈ U, R₁ (c x) = Q (R₀ x)) :
    IsLocalDiffeomorph I J n (R₁.symm ∘ Q ∘ R₀) := by
  let F := (R₀.trans Q.toHomeomorph).trans R₁.symm
  have hFc : EqOn F c U := by
    intro x hx
    change R₁.symm (Q (R₀ x)) = c x
    rw [← hcomm x hx, R₁.symm_apply_apply]
  intro x
  by_cases hx : x ∈ K
  · apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
      (hg := c.isLocalDiffeomorphAt I J n (hUc (hKU hx)))
    filter_upwards [hU.mem_nhds (hKU hx)] with z hz
    exact hFc hz
  · have hy : F x ∉ L := by
      intro h
      rw [← hcKL] at h
      obtain ⟨z, hz, hze⟩ := h
      have hFz : F z = F x := (hFc (hKU hz)).trans hze
      exact hx (F.injective hFz ▸ hz)
    have hinv := R₁.isLocalDiffeomorphAt_symm (hR₁ (F x) hy)
    have heq : R₁ (F x) = Q (R₀ x) := R₁.apply_symm_apply _
    rw [heq] at hinv
    exact ((hR₀ x hx).comp _ _ (Q.isLocalDiffeomorph _)).comp _ _ hinv

theorem exists_diffeomorph_unrounding
    (c : PartialDiffeomorph I J M N n) (R₀ : M ≃ₜ M) (R₁ : N ≃ₜ N)
    (Q : Diffeomorph I J M N n) {K : Set M} {L : Set N}
    (hR₀ : ∀ x ∉ K, IsLocalDiffeomorphAt I I n R₀ x)
    (hR₁ : ∀ y ∉ L, IsLocalDiffeomorphAt J J n R₁ y)
    (hcKL : c '' K = L) {U : Set M} (hU : IsOpen U) (hKU : K ⊆ U)
    (hUc : U ⊆ c.source) (hcomm : ∀ x ∈ U, R₁ (c x) = Q (R₀ x))
    {A : Set M} {B : Set N} (hQ : Q '' (R₀ '' A) = R₁ '' B) :
    ∃ F : Diffeomorph I J M N n,
      (F : M → N) = R₁.symm ∘ Q ∘ R₀ ∧ F '' A = B ∧ EqOn F c U := by
  let G := (R₀.trans Q.toHomeomorph).trans R₁.symm
  have hG : IsLocalDiffeomorph I J n G :=
    c.isLocalDiffeomorph_unrounding R₀ R₁ Q hR₀ hR₁ hcKL hU hKU hUc hcomm
  let F := hG.diffeomorphOfBijective G.bijective
  have hF : (F : M → N) = R₁.symm ∘ Q ∘ R₀ := rfl
  refine ⟨F, hF, ?_, ?_⟩
  · rw [hF, image_comp, image_comp, hQ, image_image]
    simp only [R₁.symm_apply_apply, image_id']
  · intro x hx
    rw [hF]
    change R₁.symm (Q (R₀ x)) = c x
    rw [← hcomm x hx, R₁.symm_apply_apply]

end PartialDiffeomorph
