/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy

open Set

namespace DifferentialGeometry.Topology

universe u

noncomputable def complementHomeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) : (Aᶜ : Set X) ≃ₜ ((e '' A)ᶜ : Set Y) :=
  e.subtype (fun x => by
    constructor
    · intro hx hy
      obtain ⟨a, ha, hea⟩ := hy
      exact hx (e.injective hea ▸ ha)
    · intro hx hAx
      exact hx ⟨x, hAx, rfl⟩)

noncomputable def integralComplementHomologyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : X ≃ₜ Y) (A : Set X) :
    integralSingularHomology n (Aᶜ : Set X) ≃ₗ[ℤ]
      integralSingularHomology n ((e '' A)ᶜ : Set Y) :=
  integralSingularHomologyHomotopyEquiv n (complementHomeomorph e A).toHomotopyEquiv

theorem subsingleton_integralComplementHomology_iff
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : X ≃ₜ Y) (A : Set X) :
    Subsingleton (integralSingularHomology n (Aᶜ : Set X)) ↔
      Subsingleton (integralSingularHomology n ((e '' A)ᶜ : Set Y)) := by
  constructor
  · intro h
    let _ := h
    exact (integralComplementHomologyEquiv n e A).symm.toEquiv.subsingleton
  · intro h
    let _ := h
    exact (integralComplementHomologyEquiv n e A).toEquiv.subsingleton

end DifferentialGeometry.Topology
