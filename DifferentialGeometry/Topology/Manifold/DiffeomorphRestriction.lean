import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_diffeomorph_restriction_to_open
    {E F H G N M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace N] [ChartedSpace H N]
    [TopologicalSpace M] [ChartedSpace G M]
    (O : TopologicalSpace.Opens N) (V R : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮I, J⟯ V) (hRV : R ≤ V) :
    ∃ U : TopologicalSpace.Opens N, ∃ hUO : U ≤ O, ∃ Ψ : U ≃ₘ⟮I, J⟯ R,
      (∀ x : O, (x : N) ∈ U ↔ (Φ x : M) ∈ R) ∧
      ∀ x : U, (Ψ x : M) = (Φ (TopologicalSpace.Opens.inclusion hUO x) : M) := by
  let A : Set O := (fun x ↦ (Φ x : M)) ⁻¹' (R : Set M)
  have hA : IsOpen A := R.isOpen.preimage (continuous_subtype_val.comp Φ.continuous)
  let U : TopologicalSpace.Opens N :=
    ⟨Subtype.val '' A, O.isOpenEmbedding'.isOpenMap A hA⟩
  have hUO : U ≤ O := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hmem (x : O) : (x : N) ∈ U ↔ (Φ x : M) ∈ R := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx : y = x) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let f : U → R := fun x ↦
    ⟨Φ (TopologicalSpace.Opens.inclusion hUO x),
      (hmem (TopologicalSpace.Opens.inclusion hUO x)).mp x.property⟩
  let g : R → U := fun y ↦
    ⟨(Φ.symm (TopologicalSpace.Opens.inclusion hRV y) : N),
      (hmem _).mpr (by simpa only [Φ.apply_symm_apply] using y.property)⟩
  let e : U ≃ R :=
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        apply Subtype.ext
        change (Φ.symm (Φ (TopologicalSpace.Opens.inclusion hUO x)) : N) = (x : N)
        rw [Φ.symm_apply_apply]
      right_inv := by
        intro y
        apply Subtype.ext
        change (Φ (Φ.symm (TopologicalSpace.Opens.inclusion hRV y)) : M) = (y : M)
        rw [Φ.apply_symm_apply] }
  have hf : ContMDiff I J ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff R f).mp
    change ContMDiff I J ∞ ((Subtype.val : V → M) ∘
      (Φ ∘ TopologicalSpace.Opens.inclusion hUO))
    exact contMDiff_subtype_val.comp (Φ.contMDiff.comp (contMDiff_inclusion hUO))
  have hg : ContMDiff J I ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff U g).mp
    change ContMDiff J I ∞ ((Subtype.val : O → N) ∘
      (Φ.symm ∘ TopologicalSpace.Opens.inclusion hRV))
    exact contMDiff_subtype_val.comp (Φ.symm.contMDiff.comp (contMDiff_inclusion hRV))
  exact ⟨U, hUO, { toEquiv := e, contMDiff_toFun := hf, contMDiff_invFun := hg },
    hmem, fun _ ↦ rfl⟩

end DifferentialGeometry.Topology.Manifold
