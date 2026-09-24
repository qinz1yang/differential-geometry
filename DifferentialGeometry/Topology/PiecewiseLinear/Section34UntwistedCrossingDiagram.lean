import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCylinderUntwisting
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FourSpokePseudoIsotopySquare

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsCylindricalDiagram.exists_untwisted_four_spoke_diagram
    {g : (ℝ × ℝ) × ℝ → E} {S : Set E} (hg : IsCylindricalDiagram g spliceSquare S)
    {u : ℝ × ℝ → ℝ × ℝ} (hu : IsPLHomeomorphOn u spliceSquare spliceSquare)
    (hends : ∀ x ∈ spliceSquare, g (x, 0) = g (u x, 1))
    (hspokes : ∀ i, u '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i))
    (hleaves : ∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf i) :
    ∃ f : (ℝ × ℝ) × ℝ → E, IsCylindricalDiagram f spliceSquare S ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = g (x, 0)) ∧
      (∀ i, f '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        g '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, f (0, t) = g (0, t)) ∧
      ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, f (fourSpokeModelLeaf i, t) = g (fourSpokeModelLeaf i, t) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦT, hΦc, hΦv⟩ :=
    exists_PL_splice_square_pseudoisotopy_of_preserves_spokes hu hspokes hleaves
  obtain ⟨hnew, hnewends, hnew0, hnewimages⟩ :=
    hg.untwist_with_marked_pseudoisotopy hu hends hΦ hΦ0 hΦ1
  exact ⟨g ∘ Φ, hnew, hnewends, hnew0,
    fun i => hnewimages _ (hΦT i), fun t ht => congrArg g (hΦc t ht),
    fun i t ht => congrArg g (hΦv i t ht)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
