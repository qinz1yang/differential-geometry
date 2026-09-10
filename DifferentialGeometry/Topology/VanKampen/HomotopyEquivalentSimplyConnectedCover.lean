/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

set_option autoImplicit false

open Set
open scoped ContinuousMap

universe u

namespace DifferentialGeometry.Topology.VanKampen

theorem simplyConnected_sourceSpaces_of_homotopyEquiv_to_cover
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (eU : K ≃ₕ U) (eV : L ≃ₕ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace X] [SimplyConnectedSpace (↑(U ∩ V))] :
    SimplyConnectedSpace K ∧ SimplyConnectedSpace L := by
  rcases simplyConnected_coverMembers_of_union U V hU hV hcover x₀ hx₀ with ⟨hSU, hSV⟩
  let _ : SimplyConnectedSpace U := hSU
  let _ : SimplyConnectedSpace V := hSV
  exact ⟨eU.simplyConnectedSpace, eV.simplyConnectedSpace⟩

end DifferentialGeometry.Topology.VanKampen
