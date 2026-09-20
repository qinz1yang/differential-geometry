/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeDisk

/-!
# Four-spoke disks presented by a chart

The consumers of the four-page extension theorem are link disks and link spheres sitting
inside a normed space of arbitrary finite dimension. There the intrinsic boundary of a
piecewise linear `2`-ball is not its ambient frontier, so the planar statement of
`FourSpokeDisk.lean` does not apply verbatim.

This file supplies the conjugated form. A piecewise linear `2`-ball `D` in a finite
dimensional normed space is presented as `u '' D₀` for a planar piecewise linear `2`-ball
`D₀` carrying planar four-spoke data; the intrinsic boundary of `D` is `u '' frontier D₀`
and the spokes are `u '' T₀ i`. The boundary homeomorphism, the spoke homeomorphisms and the
conclusion all live on the abstract side; the proof pulls them back through the two charts,
applies `exists_isPLHomeomorphOn_of_fourSpokeDisk`, and pushes the result forward again.

Such a presentation always exists: `IsPLBall 2 D` unfolds to a piecewise linear
homeomorphism from the standard `2`-simplex, and the planar coordinates of
`DiskCrosscutExtension.lean` turn that into a planar model. The presentation is carried
explicitly rather than existentially because the consumer has to name the same chart in the
marked boundary and spoke data.

## Main results

* `exists_isPLHomeomorphOn_of_fourSpokeChart`: the four-page extension theorem for
  piecewise linear `2`-balls presented by a chart.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The four-page extension theorem for charted `2`-balls.** Let `D = u '' D₀` and
`D' = u' '' D₀'` be piecewise linear `2`-balls presented by piecewise linear homeomorphisms
`u`, `u'` from planar four-spoke disks. Given a piecewise linear homeomorphism `γ` of the two
intrinsic boundaries `u '' frontier D₀` and `u' '' frontier D₀'` carrying `u (v₀ i)` to
`u' (v₀' (π i))` for a page permutation `π`, and piecewise linear homeomorphisms `Q i` of the
spokes carrying the centre to the centre and agreeing with `γ` at the boundary endpoints,
there is a piecewise linear homeomorphism `Φ` of `D` onto `D'` restricting to `γ` on the
boundary and to `Q i` on each spoke; in particular it carries each spoke onto the spoke named
by `π`. Only the source side carries cyclic-order data, in the cut pair `A₁, A₂`. -/
theorem exists_isPLHomeomorphOn_of_fourSpokeChart
    {D : Set E} {D' : Set F} {D₀ D₀' A₁ A₂ : Set Plane} {c₀ c₀' : Plane}
    {T₀ T₀' : Fin 4 → Set Plane} {v₀ v₀' : Fin 4 → Plane}
    (hD₀ : IsPLBall 2 D₀) (hD₀' : IsPLBall 2 D₀')
    (hT₀ : ∀ i, IsPLBall 1 (T₀ i)) (hT₀' : ∀ i, IsPLBall 1 (T₀' i))
    (harc : ∀ i, IsArcBetween (T₀ i) c₀ (v₀ i))
    (harc' : ∀ i, IsArcBetween (T₀' i) c₀' (v₀' i))
    (hTD : ∀ i, T₀ i ⊆ D₀) (hTD' : ∀ i, T₀' i ⊆ D₀')
    (hTf : ∀ i, T₀ i ∩ frontier D₀ = {v₀ i}) (hTf' : ∀ i, T₀' i ∩ frontier D₀' = {v₀' i})
    (hTT : ∀ i j, i ≠ j → T₀ i ∩ T₀ j = {c₀}) (hTT' : ∀ i j, i ≠ j → T₀' i ∩ T₀' j = {c₀'})
    (hcut : IsCutPair (frontier D₀) (v₀ 0) (v₀ 2) A₁ A₂)
    (hv1 : v₀ 1 ∈ A₁) (hv3 : v₀ 3 ∈ A₂)
    {u : Plane → E} (hu : IsPLHomeomorphOn u D₀ D)
    {u' : Plane → F} (hu' : IsPLHomeomorphOn u' D₀' D')
    {π : Equiv.Perm (Fin 4)} {γ : E → F}
    (hγ : IsPLHomeomorphOn γ (u '' frontier D₀) (u' '' frontier D₀'))
    (hγv : ∀ i, γ (u (v₀ i)) = u' (v₀' (π i)))
    {Q : Fin 4 → E → F} (hQ : ∀ i, IsPLHomeomorphOn (Q i) (u '' T₀ i) (u' '' T₀' (π i)))
    (hQc : ∀ i, Q i (u c₀) = u' c₀') (hQv : ∀ i, Q i (u (v₀ i)) = γ (u (v₀ i))) :
    ∃ Φ : E → F, IsPLHomeomorphOn Φ D D' ∧ EqOn Φ γ (u '' frontier D₀) ∧
      (∀ i, EqOn Φ (Q i) (u '' T₀ i)) ∧ ∀ i, Φ '' (u '' T₀ i) = u' '' T₀' (π i) := by
  classical
  have hfrsub : frontier D₀ ⊆ D₀ := hD₀.isPolyhedron.isCompact.isClosed.frontier_subset
  have hfrsub' : frontier D₀' ⊆ D₀' := hD₀'.isPolyhedron.isCompact.isClosed.frontier_subset
  have hufr : IsPLHomeomorphOn u (frontier D₀) (u '' frontier D₀) :=
    hu.restrict hD₀.isPLSphere_frontier.isPolyhedron hfrsub
  have hu'fr : IsPLHomeomorphOn u' (frontier D₀') (u' '' frontier D₀') :=
    hu'.restrict hD₀'.isPLSphere_frontier.isPolyhedron hfrsub'
  have huT : ∀ i, IsPLHomeomorphOn u (T₀ i) (u '' T₀ i) :=
    fun i => hu.restrict (hT₀ i).isPolyhedron (hTD i)
  have hu'T : ∀ i, IsPLHomeomorphOn u' (T₀' i) (u' '' T₀' i) :=
    fun i => hu'.restrict (hT₀' i).isPolyhedron (hTD' i)
  have hvfr' : ∀ i, v₀' i ∈ frontier D₀' := fun i => ((hTf' i).symm.subset rfl).2
  have hg : IsPLHomeomorphOn (Function.invFunOn u' (frontier D₀') ∘ (γ ∘ u))
      (frontier D₀) (frontier D₀') := (hufr.trans hγ).trans hu'fr.symm
  have hgv : ∀ i, (Function.invFunOn u' (frontier D₀') ∘ (γ ∘ u)) (v₀ i) = v₀' (π i) := by
    intro i
    simp only [Function.comp_apply, hγv i]
    exact hu'fr.bijOn.invOn_invFunOn.1 (hvfr' (π i))
  have hq : ∀ i, IsPLHomeomorphOn (Function.invFunOn u' (T₀' (π i)) ∘ (Q i ∘ u))
      (T₀ i) (T₀' (π i)) := fun i => ((huT i).trans (hQ i)).trans (hu'T (π i)).symm
  have hqc : ∀ i, (Function.invFunOn u' (T₀' (π i)) ∘ (Q i ∘ u)) c₀ = c₀' := by
    intro i
    simp only [Function.comp_apply, hQc i]
    exact (hu'T (π i)).bijOn.invOn_invFunOn.1 (harc' (π i)).left_mem
  have hqv : ∀ i, (Function.invFunOn u' (T₀' (π i)) ∘ (Q i ∘ u)) (v₀ i) =
      (Function.invFunOn u' (frontier D₀') ∘ (γ ∘ u)) (v₀ i) := by
    intro i
    rw [hgv i]
    simp only [Function.comp_apply, hQv i, hγv i]
    exact (hu'T (π i)).bijOn.invOn_invFunOn.1 (harc' (π i)).right_mem
  obtain ⟨Φ₀, hΦ₀, hΦ₀g, hΦ₀q⟩ := exists_isPLHomeomorphOn_of_fourSpokeDisk hD₀ hD₀' hT₀ hT₀'
    harc harc' hTD hTD' hTf hTf' hTT hTT' hcut hv1 hv3 hg hgv
    (q := fun i => Function.invFunOn u' (T₀' (π i)) ∘ (Q i ∘ u)) hq hqc hqv
  have hΦeq : EqOn (u' ∘ Φ₀ ∘ Function.invFunOn u D₀) γ (u '' frontier D₀) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hu.bijOn.invOn_invFunOn.1 (hfrsub hy), hΦ₀g hy]
    exact hu'fr.bijOn.invOn_invFunOn.2 (hγ.bijOn.mapsTo ⟨y, hy, rfl⟩)
  have hΦspoke : ∀ i, EqOn (u' ∘ Φ₀ ∘ Function.invFunOn u D₀) (Q i) (u '' T₀ i) := by
    rintro i _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hu.bijOn.invOn_invFunOn.1 (hTD i hy), hΦ₀q i hy]
    exact (hu'T (π i)).bijOn.invOn_invFunOn.2 ((hQ i).bijOn.mapsTo ⟨y, hy, rfl⟩)
  exact ⟨_, (hu.symm.trans hΦ₀).trans hu', hΦeq, hΦspoke,
    fun i => ((hΦspoke i).image_eq).trans (hQ i).image_eq⟩

end DifferentialGeometry.Topology.PiecewiseLinear
