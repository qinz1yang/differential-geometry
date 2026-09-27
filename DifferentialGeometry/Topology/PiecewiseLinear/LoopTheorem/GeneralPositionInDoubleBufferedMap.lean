/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem assemble_buffered_map_fibre_and_boundary
    {X Y : Type*}
    {S A : Set X} {H C Ostar V : Set Y} {Bd : Set X} {f g : X → Y}
    (hEqOn : EqOn g f A)
    (hEqStar : ∀ z ∈ Ostar, g ⁻¹' {z} = f ⁻¹' {z})
    (hEqOff : ∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z})
    (hFproper : S ∩ f ⁻¹' H = Bd)
    (hHiff : ∀ x ∈ S, g x ∈ H ↔ f x ∈ H)
    (hfront : Bd ⊆ A)
    (hC : C ⊆ Ostar) :
    S ∩ g ⁻¹' H = Bd ∧ EqOn g f Bd ∧
      (∀ z ∈ C, g ⁻¹' {z} = f ⁻¹' {z}) ∧
        ∀ z ∈ Ostar ∪ Vᶜ, g ⁻¹' {z} = f ⁻¹' {z} := by
  have hproperG : S ∩ g ⁻¹' H = Bd := by
    have hset : S ∩ g ⁻¹' H = S ∩ f ⁻¹' H := by
      ext x
      constructor
      · rintro ⟨hx, hgx⟩
        exact ⟨hx, (hHiff x hx).mp hgx⟩
      · rintro ⟨hx, hfx⟩
        exact ⟨hx, (hHiff x hx).mpr hfx⟩
    rw [hset, hFproper]
  have hboundary : EqOn g f Bd := by
    intro x hx
    exact hEqOn (hfront hx)
  have hEqC : ∀ z ∈ C, g ⁻¹' {z} = f ⁻¹' {z} := by
    intro z hz
    exact hEqStar z (hC hz)
  have hEqUnion : ∀ z ∈ Ostar ∪ Vᶜ, g ⁻¹' {z} = f ⁻¹' {z} := by
    intro z hz
    rcases hz with hzO | hzV
    · exact hEqStar z hzO
    · exact hEqOff z hzV
  exact ⟨hproperG, hboundary, hEqC, hEqUnion⟩

end DifferentialGeometry.Topology.PiecewiseLinear
