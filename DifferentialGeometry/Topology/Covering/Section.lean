/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

noncomputable section

universe u v

namespace Poincare.Topology

theorem exists_continuous_section_of_isCoveringMap_of_simplyConnected
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) (x₀ : X) (e₀ : E) (he₀ : p e₀ = x₀) :
    ∃ s : C(X, E), Function.RightInverse s p := by
  obtain ⟨s, ⟨_, hs⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ e₀ (by simpa using he₀)
  refine ⟨s, fun x ↦ ?_⟩
  exact congrFun hs x

end Poincare.Topology
