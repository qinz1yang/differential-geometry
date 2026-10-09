/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.EmbeddingParity
import Mathlib.Topology.OpenPartialHomeomorph.Composition

open Set Filter
open scoped Topology Manifold

noncomputable section

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ} {M : Type*} [TopologicalSpace M]

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

private theorem mem_chart_transition_source
    (c c' : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ c.source) (hx' : x ∈ c'.source) :
    c x ∈ (c.symm ≫ₕ c').source := by
  refine ⟨c.map_source hx, ?_⟩
  change c.symm (c x) ∈ c'.source
  rwa [c.left_inv hx]

def chartOrientationParity (c c' : OpenPartialHomeomorph M E) (x : M)
    (hx : x ∈ c.source) (hx' : x ∈ c'.source) : ZMod 2 :=
  embeddingOrientationParity (c.symm ≫ₕ c').open_source
    (c.symm ≫ₕ c').continuousOn (c.symm ≫ₕ c').injOn
    ⟨c x, mem_chart_transition_source c c' hx hx'⟩

theorem chartOrientationParity_eq_of_isPreconnected
    (c c' : OpenPartialHomeomorph M E) {A : Set M}
    (hA : IsPreconnected A) (hAc : A ⊆ c.source) (hAc' : A ⊆ c'.source)
    {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    chartOrientationParity c c' x (hAc hx) (hAc' hx) =
      chartOrientationParity c c' y (hAc hy) (hAc' hy) := by
  have hsource : c '' A ⊆ (c.symm ≫ₕ c').source := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_chart_transition_source c c' (hAc hz) (hAc' hz)
  exact embeddingOrientationParity_eq_of_isPreconnected
    (c.symm ≫ₕ c').open_source (c.symm ≫ₕ c').continuousOn (c.symm ≫ₕ c').injOn
    (hA.image c (c.continuousOn.mono hAc)) hsource
    (mem_image_of_mem c hx) (mem_image_of_mem c hy)

theorem chartOrientationParity_self (c : OpenPartialHomeomorph M E)
    (x : M) (hx : x ∈ c.source) : chartOrientationParity c c x hx hx = 0 := by
  have hpoint := mem_chart_transition_source c c hx hx
  have heq : (c.symm ≫ₕ c) =ᶠ[𝓝 (c x)] (id : E → E) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
    exact c.right_inv hz
  have h := embeddingOrientationParity_congr
    (c.symm ≫ₕ c).open_source c.open_target
    (c.symm ≫ₕ c).continuousOn (c.symm ≫ₕ c).injOn
    continuousOn_id (injOn_id c.target) hpoint (c.map_source hx) heq
  exact h.trans (embeddingOrientationParity_id c.open_target ⟨c x, c.map_source hx⟩)

theorem chartOrientationParity_add
    (a b c : OpenPartialHomeomorph M E) (x : M)
    (ha : x ∈ a.source) (hb : x ∈ b.source) (hc : x ∈ c.source) :
    chartOrientationParity a b x ha hb + chartOrientationParity b c x hb hc =
      chartOrientationParity a c x ha hc := by
  let f := a.symm ≫ₕ b
  let g := b.symm ≫ₕ c
  let W := (f ≫ₕ g).source
  have hW : IsOpen W := (f ≫ₕ g).open_source
  have hWf : W ⊆ f.source := inter_subset_left
  have hWg : MapsTo f W g.source := fun _ hz => hz.2
  have hax : a x ∈ f.source := mem_chart_transition_source a b ha hb
  have hbx : b x ∈ g.source := mem_chart_transition_source b c hb hc
  have hfax : f (a x) = b x := by
    change b (a.symm (a x)) = b x
    rw [a.left_inv ha]
  have hxW : a x ∈ W := by
    refine ⟨hax, ?_⟩
    change f (a x) ∈ g.source
    rw [hfax]
    exact hbx
  have hcomp := embeddingOrientationParity_comp hW g.open_source
    (f.continuousOn.mono hWf) (f.injOn.mono hWf) g.continuousOn g.injOn hWg ⟨a x, hxW⟩
  have hfrest := embeddingOrientationParity_congr hW f.open_source
    (f.continuousOn.mono hWf) (f.injOn.mono hWf) f.continuousOn f.injOn
    hxW hax Filter.EventuallyEq.rfl
  have heq : (g ∘ f) =ᶠ[𝓝 (a x)] (a.symm ≫ₕ c) := by
    filter_upwards [f.open_source.mem_nhds hax] with z hz
    change c (b.symm (b (a.symm z))) = c (a.symm z)
    have hz' : a.symm z ∈ b.source := hz.2
    rw [b.left_inv hz']
  have hrest := embeddingOrientationParity_congr hW (a.symm ≫ₕ c).open_source
    (g.continuousOn.comp (f.continuousOn.mono hWf) hWg)
    (g.injOn.comp (f.injOn.mono hWf) hWg)
    (a.symm ≫ₕ c).continuousOn (a.symm ≫ₕ c).injOn
    hxW (mem_chart_transition_source a c ha hc) heq
  rw [hfrest, hrest] at hcomp
  have hp : (⟨f (a x), hWg hxW⟩ : g.source) = ⟨b x, hbx⟩ := Subtype.ext hfax
  rw [hp] at hcomp
  exact hcomp.symm

theorem chartOrientationParity_symm
    (a b : OpenPartialHomeomorph M E) (x : M)
    (ha : x ∈ a.source) (hb : x ∈ b.source) :
    chartOrientationParity a b x ha hb = chartOrientationParity b a x hb ha := by
  have h := chartOrientationParity_add a b a x ha hb ha
  rw [chartOrientationParity_self] at h
  have hz : ∀ z : ZMod 2, z + z = 0 := by decide
  exact add_right_cancel (h.trans (hz (chartOrientationParity b a x hb ha)).symm)

end DifferentialGeometry.LocalDegree
