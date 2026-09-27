/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.ChartParity

open Set Filter
open scoped Topology Manifold

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem chartOrientationParity_pullback
    (F : OpenPartialHomeomorph M N) (c c' : OpenPartialHomeomorph N E)
    (x : M) (hx : x ∈ F.source)
    (hc : F x ∈ c.source) (hc' : F x ∈ c'.source) :
    chartOrientationParity (F ≫ₕ c) (F ≫ₕ c') x ⟨hx, hc⟩ ⟨hx, hc'⟩ =
      chartOrientationParity c c' (F x) hc hc' := by
  have heq : ((F ≫ₕ c).symm ≫ₕ (F ≫ₕ c')) =ᶠ[𝓝 (c (F x))] (c.symm ≫ₕ c') := by
    filter_upwards [(F ≫ₕ c).open_target.mem_nhds ((F ≫ₕ c).map_source ⟨hx, hc⟩)]
      with y hy
    change c' (F (F.symm (c.symm y))) = c' (c.symm y)
    rw [F.right_inv hy.2]
  unfold chartOrientationParity
  exact embeddingOrientationParity_congr
    ((F ≫ₕ c).symm ≫ₕ (F ≫ₕ c')).open_source (c.symm ≫ₕ c').open_source
    ((F ≫ₕ c).symm ≫ₕ (F ≫ₕ c')).continuousOn
    ((F ≫ₕ c).symm ≫ₕ (F ≫ₕ c')).injOn
    (c.symm ≫ₕ c').continuousOn (c.symm ≫ₕ c').injOn _ _ heq

omit [TopologicalSpace N] in
theorem chartOrientationParity_relative_eq_of_isPreconnected
    (F : OpenPartialHomeomorph M M) (c c' : OpenPartialHomeomorph M E)
    {A : Set M} (hA : IsPreconnected A) (hAc : A ⊆ c.source) (hAc' : A ⊆ c'.source)
    (x : M) (hxF : x ∈ F.source) (hx : x ∈ A) (hFx : F x ∈ A) :
    chartOrientationParity c (F ≫ₕ c) x (hAc hx) ⟨hxF, hAc hFx⟩ =
      chartOrientationParity c' (F ≫ₕ c') x (hAc' hx) ⟨hxF, hAc' hFx⟩ := by
  have h₁ := chartOrientationParity_add c c' (F ≫ₕ c) x (hAc hx) (hAc' hx)
    ⟨hxF, hAc hFx⟩
  have h₂ := chartOrientationParity_add c' (F ≫ₕ c') (F ≫ₕ c) x (hAc' hx)
    ⟨hxF, hAc' hFx⟩ ⟨hxF, hAc hFx⟩
  have h₃ := chartOrientationParity_pullback F c' c x hxF (hAc' hFx) (hAc hFx)
  have h₄ := chartOrientationParity_eq_of_isPreconnected c' c hA hAc' hAc hx hFx
  have h₅ := chartOrientationParity_symm c c' x (hAc hx) (hAc' hx)
  rw [h₃, ← h₄, ← h₅] at h₂
  rw [← h₁, ← h₂]
  have hz : ∀ s : ZMod 2, s + s = 0 := by decide
  rw [add_left_comm, hz, add_zero]

theorem chartOrientationParity_pair_eq_of_isPreconnected
    (F G : OpenPartialHomeomorph M N) (c c' : OpenPartialHomeomorph N E)
    {A : Set N} (hA : IsPreconnected A) (hAc : A ⊆ c.source) (hAc' : A ⊆ c'.source)
    (x : M) (hxF : x ∈ F.source) (hxG : x ∈ G.source)
    (hFx : F x ∈ A) (hGx : G x ∈ A) :
    chartOrientationParity (F ≫ₕ c) (G ≫ₕ c) x ⟨hxF, hAc hFx⟩ ⟨hxG, hAc hGx⟩ =
      chartOrientationParity (F ≫ₕ c') (G ≫ₕ c') x ⟨hxF, hAc' hFx⟩ ⟨hxG, hAc' hGx⟩ := by
  have h₁ := chartOrientationParity_add (F ≫ₕ c) (F ≫ₕ c') (G ≫ₕ c) x
    ⟨hxF, hAc hFx⟩ ⟨hxF, hAc' hFx⟩ ⟨hxG, hAc hGx⟩
  have h₂ := chartOrientationParity_add (F ≫ₕ c') (G ≫ₕ c') (G ≫ₕ c) x
    ⟨hxF, hAc' hFx⟩ ⟨hxG, hAc' hGx⟩ ⟨hxG, hAc hGx⟩
  have h₃ := chartOrientationParity_pullback F c c' x hxF (hAc hFx) (hAc' hFx)
  have h₄ := chartOrientationParity_pullback G c' c x hxG (hAc' hGx) (hAc hGx)
  have h₅ := chartOrientationParity_eq_of_isPreconnected c' c hA hAc' hAc hFx hGx
  have h₆ := chartOrientationParity_symm c c' (F x) (hAc hFx) (hAc' hFx)
  rw [h₃] at h₁
  rw [h₄, ← h₅, ← h₆] at h₂
  rw [← h₁, ← h₂]
  have hz : ∀ s : ZMod 2, s + s = 0 := by decide
  rw [add_left_comm, hz, add_zero]

theorem exists_relative_chart_sign_of_connected_carrier
    (F G : OpenPartialHomeomorph M N) {S : Set M} (hS : IsConnected S)
    (hSF : S ⊆ F.source) (hSG : S ⊆ G.source)
    {A : Set N} (hA : IsPreconnected A) (hFA : MapsTo F S A) (hGA : MapsTo G S A)
    (b : OpenPartialHomeomorph N E) (hAb : A ⊆ b.source) :
    ∃ σ : ZMod 2, ∀ (c : OpenPartialHomeomorph N E) (hAc : A ⊆ c.source), ∀ x (hx : x ∈ S),
      chartOrientationParity (F ≫ₕ c) (G ≫ₕ c) x
        ⟨hSF hx, hAc (hFA hx)⟩ ⟨hSG hx, hAc (hGA hx)⟩ = σ := by
  obtain ⟨x₀, hx₀⟩ := hS.nonempty
  refine ⟨chartOrientationParity (F ≫ₕ b) (G ≫ₕ b) x₀
    ⟨hSF hx₀, hAb (hFA hx₀)⟩ ⟨hSG hx₀, hAb (hGA hx₀)⟩, ?_⟩
  intro c hAc x hx
  rw [chartOrientationParity_pair_eq_of_isPreconnected F G c b hA hAc hAb x
    (hSF hx) (hSG hx) (hFA hx) (hGA hx)]
  exact chartOrientationParity_eq_of_isPreconnected (F ≫ₕ b) (G ≫ₕ b)
    hS.isPreconnected (fun _ hy => ⟨hSF hy, hAb (hFA hy)⟩)
    (fun _ hy => ⟨hSG hy, hAb (hGA hy)⟩) hx hx₀
end DifferentialGeometry.LocalDegree
