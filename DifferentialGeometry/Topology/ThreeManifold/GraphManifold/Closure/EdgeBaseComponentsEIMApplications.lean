import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeBaseComponentsEIM

/-!
# Consumer of E2: the components of the whole circle (lane S-EDGE-INT, G1)

`finite_interval_circle_components_EIM` applied to the base `Circle` with `C = univ` (compact, empty
frontier, so the domain hypothesis is vacuous): there is no interval component, there is at least
one circle component, and every circle component is a smooth embedding `S¹ → S¹`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The whole circle: no interval component, at least one circle component, each a smooth
embedding. -/
theorem circle_components_EIM :
    ∃ l : ℕ, 0 < l ∧ ∃ c : Fin l → Circle → Circle,
      ∀ j, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (c j) := by
  obtain ⟨m, l, e, a, c, ε, -, -, hc, -, -⟩ := finite_interval_circle_components_EIM
    (Base := Circle) (C := univ) isCompact_univ (fun x hx => by simp at hx)
  have hm : m = 0 := by
    have hfr : IsEmpty {x : Circle // x ∈ frontier (univ : Set Circle)} := by
      refine ⟨fun x => ?_⟩
      simpa using x.2
    have : IsEmpty (Fin m × Bool) := ε.isEmpty
    by_contra h
    exact this.false (⟨0, Nat.pos_of_ne_zero h⟩, true)
  subst hm
  have hl : 0 < l := by
    rcases e.symm ⟨connectedComponentIn univ 1, 1, mem_univ _, rfl⟩ with j | j
    · exact j.elim0
    · exact j.pos
  exact ⟨l, hl, c, hc⟩

end GC.GraphManifold.Assembly.FC39P0
