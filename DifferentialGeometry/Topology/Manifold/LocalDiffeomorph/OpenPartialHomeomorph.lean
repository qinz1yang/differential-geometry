import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

noncomputable section

open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {r : ℕ∞ω}

def toPartialDiffeomorph (e : OpenPartialHomeomorph M N)
    (he : IsLocalDiffeomorphOn I J r e e.source) : PartialDiffeomorph I J M N r where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := he.contMDiffOn
  contMDiffOn_invFun := by
    by_cases hne : e.source.Nonempty
    · obtain ⟨Φ, hs, ht, hf⟩ :=
        DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
          he e.open_source hne e.injOn
      have htarget : Φ.target = e.target := ht.trans e.image_source_eq_target
      rw [← htarget]
      apply Φ.contMDiffOn_invFun.congr
      intro y hy
      apply e.injOn
      · exact e.map_target (htarget ▸ hy)
      · exact hs ▸ Φ.map_target hy
      · change e (e.symm y) = e (Φ.symm y)
        rw [e.right_inv (htarget ▸ hy)]
        have h := Φ.right_inv hy
        rw [show (Φ : M → N) = e from hf] at h
        exact h.symm
    · have hs : e.source = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have ht : e.target = ∅ := by rw [← e.image_source_eq_target, hs, Set.image_empty]
      rw [ht]
      exact contMDiffOn_empty

@[simp] theorem toPartialDiffeomorph_toOpenPartialHomeomorph (e : OpenPartialHomeomorph M N)
    (he : IsLocalDiffeomorphOn I J r e e.source) :
    (e.toPartialDiffeomorph he).toOpenPartialHomeomorph = e := rfl

@[simp] theorem toPartialDiffeomorph_apply (e : OpenPartialHomeomorph M N)
    (he : IsLocalDiffeomorphOn I J r e e.source) (x : M) :
    e.toPartialDiffeomorph he x = e x := rfl

@[simp] theorem toPartialDiffeomorph_symm_apply (e : OpenPartialHomeomorph M N)
    (he : IsLocalDiffeomorphOn I J r e e.source) (y : N) :
    (e.toPartialDiffeomorph he).symm y = e.symm y := rfl

end OpenPartialHomeomorph
