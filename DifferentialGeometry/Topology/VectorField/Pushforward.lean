import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

set_option autoImplicit false
open Set
open scoped Manifold ContDiff
noncomputable section
namespace DifferentialGeometry.VectorField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}
  {n : ℕ∞ω}

theorem mpullback_symm_partialDiffeomorph_apply
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    (V : ∀ x : M, TangentSpace I x) {x : M} (hx : x ∈ f.source) :
    _root_.VectorField.mpullback J I f.symm V (f x) = mfderiv I J f x (V x) := by
  unfold _root_.VectorField.mpullback
  erw [inverse_mfderiv_partialDiffeomorph f.symm hn (f.map_source hx)]
  erw [f.left_inv hx]
  rfl

theorem mpullback_trans_symm_partialDiffeomorph
    (f : PartialDiffeomorph I J M N n) (g : PartialDiffeomorph J K N P n) (hn : n ≠ 0)
    (V : ∀ y : N, TangentSpace J y) {x : M} (hx : x ∈ f.source) (hg : f x ∈ g.source) :
    _root_.VectorField.mpullback I K (f.trans g)
        (_root_.VectorField.mpullback K J g.symm V) x =
      _root_.VectorField.mpullback I J f V x := by
  have hv := mpullback_symm_partialDiffeomorph_apply g hn V hg
  change (mfderiv I K (g ∘ f) x).inverse
    (_root_.VectorField.mpullback K J g.symm V (g (f x))) = _
  rw [hv]
  erw [mfderiv_comp x (g.mdifferentiableAt hn hg) (f.mdifferentiableAt hn hx)]
  have hi := isInvertible_mfderiv_partialDiffeomorph g hn hg
  rw [hi.inverse_comp_apply_of_left, hi.inverse_apply_self]
  rfl

end DifferentialGeometry.VectorField
