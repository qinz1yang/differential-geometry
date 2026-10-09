/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfaceArcSmoothing

open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]

theorem exists_smooth_segment_in_charts (h : M ≃ₜ N)
    (a : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane M ∞)
    (b : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) N Plane ∞)
    {τa τb ρ₀ W : ℝ} (hρ₀ : 0 < ρ₀) (hρW : ρ₀ ≤ W)
    (hab : τa + 2 * ρ₀ < τb - 2 * ρ₀)
    (hR : planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W ⊆ a.source)
    (hRb : ∀ v ∈ planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W, h (a v) ∈ b.source)
    (hends : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h
      (a '' (ball (Plane.mk τa 0) ρ₀ ∪ ball (Plane.mk τb 0) ρ₀)))
    (has : ∀ t ∈ Icc (0 : ℝ) 1, Plane.mk t 0 ∈ a.source)
    (htail : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ τa ∨ τb ≤ t →
      IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h (a (Plane.mk t 0))) :
    ∃ g : M ≃ₜ N,
      EqOn g h (a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W)ᶜ ∧
      g '' (a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W) =
        h '' (a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a (Plane.mk t 0))) ∧
      ∀ x ∉ a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W,
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x := by
  obtain ⟨ρ, hρ, -, δ, hδ, -, g, hgout, hgimage, hgends, hglocal, -, hgpreserve⟩ :=
    h.exists_smooth_arc_in_charts a b hρ₀ hρW hab hR hRb hends
  refine ⟨g, hgout, hgimage, ?_, hgpreserve⟩
  intro t ht
  by_cases htin : τa - 3 * ρ < t ∧ t < τb + 3 * ρ
  · apply hglocal ⟨a (Plane.mk t 0), Plane.mk t 0, ?_, rfl⟩
    change τa - 3 * ρ < t ∧ t < τb + 3 * ρ ∧ -δ < 0 ∧ 0 < δ
    exact ⟨htin.1, htin.2, by linarith, hδ⟩
  · have htends : t < τa - ρ ∨ τb + ρ < t := by
      rcases le_or_gt t (τa - 3 * ρ) with hleft | hleft
      · exact Or.inl (by linarith)
      · exact Or.inr (by have hr := not_lt.mp (fun hr => htin ⟨hleft, hr⟩); linarith)
    have hth : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h (a (Plane.mk t 0)) :=
      htail t ht (htends.elim (fun h => Or.inl (by linarith))
        (fun h => Or.inr (by linarith)))
    let V := a.source ∩ {v : Plane | |v 1| < δ} ∩
      {v : Plane | v 0 < τa - ρ ∨ τb + ρ < v 0}
    have hV : IsOpen V := (a.open_source.inter
      (isOpen_lt (Plane.continuous_coord 1).abs continuous_const)).inter
      ((isOpen_lt (Plane.continuous_coord 0) continuous_const).union
        (isOpen_lt continuous_const (Plane.continuous_coord 0)))
    have htV : Plane.mk t 0 ∈ V := ⟨⟨has t ht, by simpa using hδ⟩, htends⟩
    have hVa : V ⊆ a.source := fun _ hv => hv.1.1
    have hVaopen : IsOpen (a '' V) :=
      a.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVa
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ hth
    filter_upwards [hVaopen.mem_nhds ⟨Plane.mk t 0, htV, rfl⟩] with y hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact hgends v hv.1.1 hv.1.2 (hv.2.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))

end Homeomorph
