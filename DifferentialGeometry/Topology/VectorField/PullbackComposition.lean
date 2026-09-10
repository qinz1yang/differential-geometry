import DifferentialGeometry.Topology.VectorField.Pushforward

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.VectorField


theorem mpullback_trans_partialDiffeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F G H H' H'' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [TopologicalSpace P] [ChartedSpace H'' P]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}
    {n : ℕ∞ω} (f : PartialDiffeomorph I J M N n) (g : PartialDiffeomorph J K N P n)
    (hn : n ≠ 0) (V : ∀ p : P, TangentSpace K p)
    {x : M} (hx : x ∈ f.source) (hg : f x ∈ g.source) :
    _root_.VectorField.mpullback I K (f.trans g) V x =
      _root_.VectorField.mpullback I J f (_root_.VectorField.mpullback J K g V) x := by
  change _root_.VectorField.mpullback I K (g ∘ f) V x = _
  unfold _root_.VectorField.mpullback
  erw [mfderiv_comp x (g.mdifferentiableAt hn hg) (f.mdifferentiableAt hn hx)]
  exact (isInvertible_mfderiv_partialDiffeomorph g hn hg).inverse_comp_apply_of_left

end Poincare.VectorField
