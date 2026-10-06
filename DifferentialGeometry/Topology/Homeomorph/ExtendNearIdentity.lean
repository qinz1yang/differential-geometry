import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Homeomorph.Defs
/-!
# Extending near-identity homeomorphisms by the identity

A self-homeomorphism `g` of a subset `V` of a metric space that moves every point `x` by less than
`infDist x Vᶜ` extends by the identity off `V` to a continuous self-map of the whole space
(`exists_homeomorph_extend_of_dist_lt_infDist`). If `g` moves `x` by less than half of
`infDist x Vᶜ`, then `g⁻¹` satisfies the previous bound, so both extensions are continuous and
together form a homeomorphism of the space (`exists_homeomorph_extend_of_dist_lt`).
-/

set_option autoImplicit false

namespace DifferentialGeometry.Topology

universe u

open Set Metric

theorem exists_homeomorph_extend_of_dist_lt_infDist {X : Type u} [MetricSpace X] {V : Set X}
    (g : V ≃ₜ V) (hg : ∀ x : V, dist (g x : X) x < Metric.infDist (x : X) Vᶜ) :
    ∃ G : X → X, Continuous G ∧ (∀ x : V, G x = g x) ∧ Set.EqOn G id Vᶜ := by
  classical
  have hV : IsOpen V := by
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨infDist x Vᶜ, dist_nonneg.trans_lt (hg ⟨x, hx⟩), ?_⟩
    intro y hy
    by_contra hyV
    have h := infDist_le_dist_of_mem (x := x) (show y ∈ Vᶜ from hyV)
    rw [mem_ball, dist_comm] at hy
    linarith
  let G : X → X := fun x => if h : x ∈ V then (g ⟨x, h⟩ : X) else x
  have hGV : ∀ x : V, G x = g x := fun x => dite_eq_left x.2
  have hGc : ∀ x, x ∉ V → G x = x := fun x hx => dite_eq_right hx
  have hGon : ContinuousOn G V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : V.domRestrict G = fun x : V => (g x : X) := funext hGV
    rw [h]
    exact continuous_subtype_val.comp g.continuous
  refine ⟨G, ?_, hGV, fun x hx => hGc x hx⟩
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx₀ : x₀ ∈ V
  · exact hGon.continuousAt (hV.mem_nhds hx₀)
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε / 2, by positivity, ?_⟩
  intro x hx
  rw [hGc x₀ hx₀]
  by_cases hxV : x ∈ V
  · rw [hGV ⟨x, hxV⟩]
    have h1 := hg ⟨x, hxV⟩
    have h2 : infDist x Vᶜ ≤ dist x x₀ := infDist_le_dist_of_mem hx₀
    have h3 := dist_triangle (g ⟨x, hxV⟩ : X) x x₀
    simp only at h1
    linarith
  · rw [hGc x hxV]
    linarith

theorem exists_homeomorph_extend_of_dist_lt {X : Type u} [MetricSpace X] {V : Set X}
    (g : V ≃ₜ V) (hg : ∀ x : V, dist (g x : X) x < Metric.infDist (x : X) Vᶜ / 2) :
    ∃ G : X ≃ₜ X, (∀ x : V, G x = g x) ∧ Set.EqOn G id Vᶜ := by
  obtain ⟨F, hF, hFV, hFc⟩ := exists_homeomorph_extend_of_dist_lt_infDist g (fun x => by
    have h := hg x
    have h0 := dist_nonneg (x := (g x : X)) (y := x)
    linarith)
  obtain ⟨F', hF', hF'V, hF'c⟩ := exists_homeomorph_extend_of_dist_lt_infDist g.symm (by
    intro y
    have h1 := hg (g.symm y)
    rw [g.apply_symm_apply, dist_comm] at h1
    have h2 := infDist_le_infDist_add_dist (x := ((g.symm y : V) : X)) (y := (y : X))
      (s := Vᶜ)
    linarith)
  refine ⟨
    { toFun := F
      invFun := F'
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := hF
      continuous_invFun := hF' }, hFV, hFc⟩
  · intro x
    by_cases hx : x ∈ V
    · rw [show x = ((⟨x, hx⟩ : V) : X) from rfl, hFV, hF'V, g.symm_apply_apply]
    · rw [hFc hx, id, hF'c hx, id]
  · intro y
    by_cases hy : y ∈ V
    · rw [show y = ((⟨y, hy⟩ : V) : X) from rfl, hF'V, hFV, g.apply_symm_apply]
    · rw [hF'c hy, id, hFc hy, id]

end DifferentialGeometry.Topology
