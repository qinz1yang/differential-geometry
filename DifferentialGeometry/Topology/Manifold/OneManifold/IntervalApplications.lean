import DifferentialGeometry.Topology.Manifold.OneManifold.IntervalOrCircle

/-!
# Applications of the classification of compact one-manifolds with boundary

* the interval itself: `[a, b]` (any `a < b`) is diffeomorphic to `[0, 1]`, and `[0, 1]` has
  exactly two boundary points (agreeing with Mathlib's `boundary_Icc`);
* the base classification used by lanes W4-EDP (FDC02) and W4-FCb (FC40): a compact smooth
  one-manifold with boundary, given as a finite union of clopen pieces, has each piece an
  interval or a circle (`finite_connectedComponents_and_Icc_or_circle` instantiated on the
  disjoint union `Icc 0 1 ⊕ Icc 0 1`, a two-interval base).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

theorem nonempty_diffeomorph_Icc_of_lt {a b : ℝ} [Fact (a < b)] :
    Nonempty (Icc a b ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) := by
  have : ConnectedSpace (Icc a b) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (Fact.out : a < b).le)
  have : Fact (a ≤ b) := ⟨(Fact.out : a < b).le⟩
  exact nonempty_diffeomorph_Icc_of_boundary_nonempty ⟨⊥, Icc_isBoundaryPoint_bot⟩

theorem ncard_boundary_Icc_of_lt {a b : ℝ} [Fact (a < b)] :
    ((𝓡∂ 1).boundary (Icc a b)).ncard = 2 := by
  have : ConnectedSpace (Icc a b) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (Fact.out : a < b).le)
  have : Fact (a ≤ b) := ⟨(Fact.out : a < b).le⟩
  exact ncard_boundary_eq_two_of_boundary_nonempty ⟨⊥, Icc_isBoundaryPoint_bot⟩

theorem nonempty_diffeomorph_Icc_self : Nonempty (Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) :=
  nonempty_diffeomorph_Icc_of_lt

/-- Two disjoint intervals: every component is an interval or a circle, and there are finitely
many components. -/
theorem two_intervals_components :
    Finite (ConnectedComponents (Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1)) ∧ ∀ x : Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1,
      Nonempty (componentOpens x ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) ∨
        Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ componentOpens x) :=
  finite_connectedComponents_and_Icc_or_circle

end DifferentialGeometry.Topology.Manifold.OneManifold
