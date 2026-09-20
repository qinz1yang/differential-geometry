/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellBoundaryExample
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.ChartComplexPiece
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.StageTransport

/-!
# The controlled inward push

The first sentence of Moise's proof of Theorem 35.2, printed p. 251, is that `K` can be moved
into `Int K` by a piecewise linear homeomorphism which is as close to the identity as we
please.  `SkeletonReduction.lean` records that sentence as `Moise352InwardPush` and reports
that the tree's inward push,
`IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward`, carries no tolerance.

This file supplies the tolerance, and the piecewise linear inverse, in the setting where the
tree's collar lives: a finite combinatorial three-manifold with boundary inside a finite
dimensional normed space.

## The mechanism

The exact push of `BoundaryInwardPush.lean` is a collar reparametrisation: on a collar
`ρ : B × [0,1] ≃ W` of the boundary it replaces the collar coordinate `t` by
`collarInwardMap g a`, that is by `max t (min (t + g y) ((t + a) / 2))`.  The record in
`SkeletonReduction.lean`, that the push height there is an uncontrolled infimum of collar
heights, conflates the two parameters.  The constant `a` is a *thinness* bound: it is chosen
small enough that the push is the identity on the part of the collar meeting the complementary
polyhedron `R`, and so it may not be lowered at will.  The height by which points actually
move is bounded by `g`, and `g` is free.  Taking `g` to be a small positive constant therefore
bounds the collar displacement by that constant, and uniform continuity of `h ∘ ρ` on the
compact collar converts this into a bound on `dist (h (p x)) (h x)`.

The inverse is `collarOutwardMap`, `s ↦ max 0 (min s (max (s - g y) (2 * s - a)))`, a
piecewise affine left inverse of `collarInwardMap` on `[0, ∞)` which is again the identity
above the level `a`, so that it glues with the identity across the same seam.

## Main results

* `collarOutwardMap` and `collarOutwardMap_collarInwardMap`: the piecewise affine left
  inverse of the collar push.
* `IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn`: the controlled push relative
  to an abstract collar, together with its left inverse.
* `IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_inward_dist_lt`: the
  controlled push of a finite combinatorial three-manifold with boundary off its boundary
  complex, with a piecewise affine left inverse and an arbitrary continuous positive
  tolerance measured after a continuous map into a metric space.
* `IsPolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt`: the conclusion of
  `Moise352InwardPush 3` verbatim, for a *compact* polyhedral three-manifold with boundary
  inside a piecewise linear three-manifold.
* `exists_frontier_nonempty_forall_exists_isPLOn_injOn_leftInvOn_dist_lt`: that conclusion at a
  set with nonempty frontier, which the boundaryless witness of `SkeletonReduction.lean` does
  not exercise.

What is **not** proved here is the locally finite case, which is what `Moise352InwardPush`
asks for.  The obstruction is recorded at the end of this file.

## Two facts about `IsPLOn` used throughout

`IsPLWithinAt` is not monotone in its set, because the polytopes witnessing
`IsPiecewiseAffineWithinAt` are required to lie inside the set.  It *is* monotone along a set
which is a neighbourhood within the larger one, and in particular along an open subset;
`IsPLWithinAt.mono_of_mem_nhdsWithin` and `IsPLOn.mono_of_isOpen` record this.  The same
observation upgrades piecewise linearity on an open set to piecewise linearity at each of its
points, and hence gives the composition rule `IsPLOn.comp_of_isOpen`, which is the missing
composition lemma for `IsPLOn` between two manifolds: the outer map only has to be piecewise
linear on an *open* set containing the image of the inner one.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section PLLocal

variable {n m p : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]

/-- Piecewise linearity within a set passes to a smaller set which is a neighbourhood of the
point within the larger one.

Unrestricted monotonicity fails: the polytopes witnessing `IsPiecewiseAffineWithinAt` must lie
inside the set. -/
theorem IsPLWithinAt.mono_of_mem_nhdsWithin {f : M → N} {s t : Set M} {x : M}
    (hf : IsPLWithinAt n m f s x) (hts : t ⊆ s) (ht : t ∈ 𝓝[s] x) :
    IsPLWithinAt n m f t x := by
  have h := (piecewiseAffineProperty_localInvariantProp (n := n)
    (m := m)).liftPropWithinAt_inter' (g := f) ht
  rw [inter_eq_right.mpr hts] at h
  exact h.mpr hf

/-- Piecewise linearity on a set passes to an open subset. -/
theorem IsPLOn.mono_of_isOpen {f : M → N} {s t : Set M} (hf : IsPLOn n m f s) (ht : IsOpen t)
    (hts : t ⊆ s) : IsPLOn n m f t := fun x hx =>
  IsPLWithinAt.mono_of_mem_nhdsWithin (hf x (hts hx)) hts
    (mem_nhdsWithin_of_mem_nhds (ht.mem_nhds hx))

/-- A map piecewise linear on an open set is piecewise linear at each point of that set. -/
theorem IsPLOn.isPLAt_of_isOpen {f : M → N} {s : Set M} (hf : IsPLOn n m f s) (hs : IsOpen s)
    {x : M} (hx : x ∈ s) : IsPLAt n m f x := by
  have hnb : s ∈ 𝓝[(univ : Set M)] x := by
    rw [nhdsWithin_univ]
    exact hs.mem_nhds hx
  have h := (piecewiseAffineProperty_localInvariantProp (n := n)
    (m := m)).liftPropWithinAt_inter' (g := f) hnb
  rw [univ_inter] at h
  exact h.mp (hf x hx)

/-- A globally piecewise linear map is piecewise linear on every open set. -/
theorem IsPL.isPLOn_of_isOpen {f : M → N} (hf : IsPL n m f) {s : Set M} (hs : IsOpen s) :
    IsPLOn n m f s := fun x hx =>
  IsPLWithinAt.mono_of_mem_nhdsWithin (show IsPLWithinAt n m f univ x from hf x) (subset_univ s)
    (by rw [nhdsWithin_univ]; exact hs.mem_nhds hx)

/-- **Composition of piecewise linear maps between manifolds**, when the outer map is
piecewise linear on an open set containing the image of the inner one.

This is the composition rule that `IsPL.comp_isPLOn` lacks: there the outer map has to be
piecewise linear everywhere.  Openness of `W` cannot be dropped, since `IsPLWithinAt` is not
monotone in its set. -/
theorem IsPLOn.comp_of_isOpen {f : M → N} {g : N → P} {s : Set M} {W : Set N}
    (hg : IsPLOn m p g W) (hW : IsOpen W) (hf : IsPLOn n m f s) (hmap : MapsTo f s W) :
    IsPLOn n p (g ∘ f) s :=
  fun x hx => IsPLAt.comp_isPLWithinAt (hg.isPLAt_of_isOpen hW (hmap hx)) (hf x hx)

end PLLocal

section CollarOrder

variable {E : Type*}

/-- The piecewise affine left inverse of `collarInwardMap`.

`collarInwardMap g a` raises the collar coordinate `t` to `max t (min (t + g y) ((t + a) / 2))`,
which is `t + g y` below the level `a - 2 * g y`, then `(t + a) / 2`, and the identity above
the level `a`.  The formula below inverts all three branches at once and clamps at `0`, so that
it maps the collar into itself. -/
noncomputable def collarOutwardMap (g : E → ℝ) (a : ℝ) (x : E × ℝ) : E × ℝ :=
  (x.1, max 0 (min x.2 (max (x.2 - g x.1) (2 * x.2 - a))))

@[simp]
theorem collarOutwardMap_fst (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    (collarOutwardMap g a x).1 = x.1 := rfl

/-- The outward map does not raise the collar coordinate. -/
theorem collarOutwardMap_snd_le (g : E → ℝ) (a : ℝ) {x : E × ℝ} (hx : 0 ≤ x.2) :
    (collarOutwardMap g a x).2 ≤ x.2 :=
  max_le hx (min_le_left _ _)

/-- The outward map never leaves the collar. -/
theorem le_collarOutwardMap_snd (g : E → ℝ) (a : ℝ) (x : E × ℝ) :
    0 ≤ (collarOutwardMap g a x).2 := le_max_left _ _

/-- Above the level `a` the outward map is the identity, which is what lets it be glued with
the identity across the same seam as `collarInwardMap`. -/
theorem collarOutwardMap_eq_self_of_le (g : E → ℝ) {a : ℝ} {x : E × ℝ} (ha : a ≤ x.2)
    (hx : 0 ≤ x.2) : collarOutwardMap g a x = x := by
  refine Prod.ext rfl ?_
  change max 0 (min x.2 (max (x.2 - g x.1) (2 * x.2 - a))) = x.2
  have hge : x.2 ≤ max (x.2 - g x.1) (2 * x.2 - a) :=
    le_max_of_le_right (by linarith)
  rw [min_eq_left hge, max_eq_right hx]

/-- **The outward map inverts the inward map.**

Only nonnegativity of the collar coordinate and of the push height is needed; the thinness
parameter `a` is arbitrary. -/
theorem collarOutwardMap_collarInwardMap (g : E → ℝ) (a : ℝ) {x : E × ℝ} (hg : 0 ≤ g x.1)
    (hx : 0 ≤ x.2) : collarOutwardMap g a (collarInwardMap g a x) = x := by
  refine Prod.ext rfl ?_
  set t := x.2 with ht
  set u := g x.1 with hu
  have hfst : (collarInwardMap g a x).1 = x.1 := rfl
  have hsnd : (collarInwardMap g a x).2 = max t (min (t + u) ((t + a) / 2)) := rfl
  change max 0 (min (collarInwardMap g a x).2
    (max ((collarInwardMap g a x).2 - g (collarInwardMap g a x).1)
      (2 * (collarInwardMap g a x).2 - a))) = t
  rw [hfst, hsnd, ← hu]
  by_cases hat : a ≤ t
  · have hmin : min (t + u) ((t + a) / 2) ≤ t := (min_le_right _ _).trans (by linarith)
    rw [max_eq_left hmin]
    have hge : t ≤ max (t - u) (2 * t - a) := le_max_of_le_right (by linarith)
    rw [min_eq_left hge, max_eq_right hx]
  · have hta : t < a := lt_of_not_ge hat
    have hmin : t ≤ min (t + u) ((t + a) / 2) := le_min (by linarith) (by linarith)
    rw [max_eq_right hmin]
    rcases le_total (t + u) ((t + a) / 2) with hle | hle
    · rw [min_eq_left hle]
      have h1 : t + u - u = t := by ring
      have h2 : 2 * (t + u) - a ≤ t := by linarith
      rw [h1, max_eq_left h2, min_eq_right (by linarith : t ≤ t + u), max_eq_right hx]
    · rw [min_eq_right hle]
      have h2 : 2 * ((t + a) / 2) - a = t := by ring
      have h1 : (t + a) / 2 - u ≤ t := by linarith
      rw [h2, max_eq_right h1, min_eq_right (by linarith : t ≤ (t + a) / 2), max_eq_right hx]

/-- The outward map preserves the model collar. -/
theorem collarOutwardMap_mapsTo_prod_Icc (g : E → ℝ) (a : ℝ) {b : ℝ} (B : Set E) :
    MapsTo (collarOutwardMap g a) (B ×ˢ Icc 0 b) (B ×ˢ Icc 0 b) := by
  intro x hx
  exact ⟨hx.1, le_collarOutwardMap_snd g a x,
    (collarOutwardMap_snd_le g a hx.2.1).trans hx.2.2⟩

end CollarOrder

section CollarMetric

variable {E : Type*} [NormedAddCommGroup E]

/-- **The displacement bound for the collar push.**

The push raises the collar coordinate by at most the value of `g` at the base point, and fixes
the base point, so the whole displacement is bounded by `g`.  This is what makes the push as
close to the identity as one pleases: `g` is an arbitrary nonnegative piecewise affine
function. -/
theorem dist_collarInwardMap_le {g : E → ℝ} (a : ℝ) {x : E × ℝ} (hg : 0 ≤ g x.1) :
    dist (collarInwardMap g a x) x ≤ g x.1 := by
  rw [Prod.dist_eq, collarInwardMap_fst]
  refine max_le (by simpa using hg) ?_
  have hge : x.2 ≤ (collarInwardMap g a x).2 := le_collarInwardMap_snd g a x
  have hle : (collarInwardMap g a x).2 ≤ x.2 + g x.1 :=
    max_le (by linarith) (min_le_left _ _)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

end CollarMetric

section Inward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The outward collar map is piecewise affine whenever the push height is. -/
theorem isPiecewiseAffineOn_collarOutwardMap {g : E → ℝ}
    (hg : IsPiecewiseAffineOn g univ) (a : ℝ) :
    IsPiecewiseAffineOn (collarOutwardMap g a) univ := by
  have hfst : IsPiecewiseAffineOn (Prod.fst : E × ℝ → E) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ E ℝ).toAffineMap isOpen_univ
  have hsnd : IsPiecewiseAffineOn (Prod.snd : E × ℝ → ℝ) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ E ℝ).toAffineMap isOpen_univ
  have hgfst : IsPiecewiseAffineOn (fun x : E × ℝ => g x.1) univ := by
    simpa only [preimage_univ, inter_univ, Function.comp_def] using hg.comp hfst
  have hneg : IsPiecewiseAffineOn (fun x : E × ℝ => -g x.1) univ := by
    have h := hgfst.affine_comp (AffineMap.const ℝ ℝ (0 : ℝ) - AffineMap.id ℝ ℝ)
    simpa only [Function.comp_def, AffineMap.coe_sub, AffineMap.coe_const, AffineMap.coe_id,
      Pi.sub_apply, Function.const_apply, id_eq, zero_sub] using h
  have hzero : IsPiecewiseAffineOn (fun _ : E × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (E × ℝ) (0 : ℝ)) isOpen_univ
  let A : (E × ℝ) →ᵃ[ℝ] ℝ :=
    (2 : ℝ) • (LinearMap.snd ℝ E ℝ).toAffineMap + AffineMap.const ℝ (E × ℝ) (-a)
  have hA : IsPiecewiseAffineOn (fun x : E × ℝ => 2 * x.2 - a) univ := by
    convert isPiecewiseAffineOn_of_affine A isOpen_univ using 1
    ext x
    change 2 * x.2 - a = (2 : ℝ) * x.2 + -a
    ring
  exact hfst.prod_mk (hzero.max (hsnd.min ((hsnd.add hneg).max hA)))

/-- **The controlled inward push relative to a collar.**

The hypotheses are those of `IsPLHomeomorphOn.exists_injective_piecewiseAffineOn_inward` with
the fixed subpolyhedron taken empty, plus a compactness hypothesis on the boundary surface and
a continuous map `h` into a metric space against which the tolerance is measured.

The conclusion adds two things to the exact push: the displacement measured after `h` is
smaller than the prescribed `ε`, and there is a piecewise affine left inverse defined on the
whole of `W ∪ R`.  Both come from the collar formula: the push height is the free parameter
`g`, taken here to be a small positive constant, and `collarOutwardMap` inverts the
reparametrisation. -/
theorem IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn
    {B W R : Set E} {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W)
    (hW : IsPolyhedron W) (hR : IsPolyhedron R) (hBR : Disjoint B R) (hBc : IsCompact B)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {Z : Type*} [MetricSpace Z] {h : E → Z}
    (hh : ContinuousOn h W) {ε : ℝ} (hε : 0 < ε) :
    ∃ f f' : E → E, IsPiecewiseAffineOn f (W ∪ R) ∧ InjOn f (W ∪ R) ∧
      MapsTo f (W ∪ R) (W ∪ R) ∧ (∀ x ∈ W ∪ R, f x ∉ B) ∧
      IsPiecewiseAffineOn f' (W ∪ R) ∧ MapsTo f' (W ∪ R) (W ∪ R) ∧
      LeftInvOn f' f (W ∪ R) ∧ ∀ x ∈ W ∪ R, dist (h (f x)) (h x) < ε := by
  classical
  let U := B ×ˢ Icc (0 : ℝ) 1
  let τ := Function.invFunOn ρ U
  have hτ : MapsTo τ W U := hρ.symm.bijOn.mapsTo
  have hleft : LeftInvOn τ ρ U := hρ.bijOn.invOn_invFunOn.1
  have hright : RightInvOn τ ρ W := hρ.bijOn.invOn_invFunOn.2
  have hBW : B ⊆ W := fun x hx =>
    hbottom x hx ▸ hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  have hboundary : ∀ z ∈ U, ρ z ∈ B ↔ z.2 = 0 := by
    intro z hz
    constructor
    · intro hB
      have heq : z = (ρ z, 0) := hρ.bijOn.injOn hz
        ⟨hB, le_rfl, zero_le_one⟩ (hbottom _ hB).symm
      exact congrArg Prod.snd heq
    · intro hzero
      have heq : z = (z.1, 0) := Prod.ext rfl hzero
      rw [heq, hbottom _ hz.1]
      exact hz.1
  have hheight : ∀ x ∈ W ∩ R, 0 < (τ x).2 := by
    intro x hx
    have hne : (τ x).2 ≠ 0 := by
      intro hzero
      have hxB : x ∈ B := by
        rw [← hright hx.1]
        exact (hboundary _ (hτ hx.1)).mpr hzero
      exact Set.disjoint_left.mp hBR hxB hx.2
    exact lt_of_le_of_ne (hτ hx.1).2.1 hne.symm
  obtain ⟨r, hr, hrheight⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ W ∩ R, r ≤ (τ x).2 := by
    by_cases hne : (W ∩ R).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (hW.isCompact.inter_right hR.isClosed).exists_isMinOn hne
        (hρ.isPiecewiseAffineOn_invFunOn.continuousOn.snd.mono inter_subset_left)
      exact ⟨(τ x).2, hheight x hx, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  set a := min r 1 with hadef
  have ha : 0 < a := lt_min hr zero_lt_one
  have haone : a ≤ 1 := min_le_right _ _
  have hthin : ∀ x ∈ W ∩ R, a ≤ (τ x).2 :=
    fun x hx => (min_le_left _ _).trans (hrheight x hx)
  have hUc : IsCompact U := hBc.prod isCompact_Icc
  have hhρ : ContinuousOn (fun z => h (ρ z)) U :=
    hh.comp hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn.mapsTo
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hUc.uniformContinuousOn_of_continuous hhρ) ε hε
  set c := δ / 2 with hcdef
  have hc : 0 < c := by positivity
  set g : E → ℝ := fun _ => c with hgdef
  have hgpos : ∀ y : E, 0 ≤ g y := fun _ => hc.le
  have hgpl : IsPiecewiseAffineOn g univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E c) isOpen_univ
  set H := collarInwardMap g a with hHdef
  set H' := collarOutwardMap g a with hH'def
  have hHU : MapsTo H U U := collarInwardMap_mapsTo_prod_Icc g haone B
  have hH'U : MapsTo H' U U := collarOutwardMap_mapsTo_prod_Icc g a B
  set Q : E → E := ρ ∘ H ∘ τ with hQdef
  set Q' : E → E := ρ ∘ H' ∘ τ with hQ'def
  have hQW : MapsTo Q W W := hρ.bijOn.mapsTo.comp (hHU.comp hτ)
  have hQ'W : MapsTo Q' W W := hρ.bijOn.mapsTo.comp (hH'U.comp hτ)
  have hQpl : IsPiecewiseAffineOn Q W := by
    have hHτ : IsPiecewiseAffineOn (H ∘ τ) W := by
      have hcomp := (isPiecewiseAffineOn_collarInwardMap hgpl a).comp
        hρ.isPiecewiseAffineOn_invFunOn
      simpa only [preimage_univ, inter_univ] using hcomp
    have hcomp := hρ.isPiecewiseAffineOn.comp hHτ
    have hinter : W ∩ (H ∘ τ) ⁻¹' U = W := inter_eq_left.mpr (hHU.comp hτ)
    rwa [hinter] at hcomp
  have hQ'pl : IsPiecewiseAffineOn Q' W := by
    have hHτ : IsPiecewiseAffineOn (H' ∘ τ) W := by
      have hcomp := (isPiecewiseAffineOn_collarOutwardMap hgpl a).comp
        hρ.isPiecewiseAffineOn_invFunOn
      simpa only [preimage_univ, inter_univ] using hcomp
    have hcomp := hρ.isPiecewiseAffineOn.comp hHτ
    have hinter : W ∩ (H' ∘ τ) ⁻¹' U = W := inter_eq_left.mpr (hH'U.comp hτ)
    rwa [hinter] at hcomp
  have hQinj : InjOn Q W := by
    intro x hx y hy hxy
    apply hρ.symm.bijOn.injOn hx hy
    exact collarInwardMap_injective g a
      (hρ.bijOn.injOn (hHU (hτ hx)) (hHU (hτ hy)) hxy)
  have hQfixed : ∀ x ∈ W, a ≤ (τ x).2 → Q x = x := by
    intro x hx ht
    change ρ (collarInwardMap g a (τ x)) = x
    rw [collarInwardMap_eq_self_of_le g ht]
    exact hright hx
  have hQ'fixed : ∀ x ∈ W, a ≤ (τ x).2 → Q' x = x := by
    intro x hx ht
    change ρ (collarOutwardMap g a (τ x)) = x
    rw [collarOutwardMap_eq_self_of_le g ht (hτ hx).2.1]
    exact hright hx
  have hQR : EqOn Q id (W ∩ R) := fun x hx => hQfixed x hx.1 (hthin x hx)
  have hQ'R : EqOn Q' id (W ∩ R) := fun x hx => hQ'fixed x hx.1 (hthin x hx)
  have hQpreR : ∀ x ∈ W, Q x ∈ R → Q x = x := by
    intro x hx hRmem
    have heq : τ (Q x) = H (τ x) := hleft (hHU (hτ hx))
    have hhigh : a ≤ (H (τ x)).2 := by
      rw [← heq]
      exact hthin (Q x) ⟨hQW hx, hRmem⟩
    apply hQfixed x hx
    by_contra hlt
    exact (not_lt_of_ge hhigh) (collarInwardMap_snd_lt_of_lt g (lt_of_not_ge hlt))
  have hQnotB : ∀ x ∈ W, Q x ∉ B := by
    intro x hx hmem
    have hz : (H (τ x)).2 = 0 := (hboundary _ (hHU (hτ hx))).mp hmem
    obtain ⟨-, hgz⟩ := (collarInwardMap_snd_eq_zero_iff ha (hgpos _) (hτ hx).2.1).mp hz
    exact hc.ne' hgz
  have hQQ' : ∀ x ∈ W, Q' (Q x) = x := by
    intro x hx
    have heq : τ (Q x) = H (τ x) := hleft (hHU (hτ hx))
    change ρ (collarOutwardMap g a (τ (Q x))) = x
    rw [heq,
      collarOutwardMap_collarInwardMap g a (x := τ x) (hgpos (τ x).1) (hτ hx).2.1]
    exact hright hx
  have hQdist : ∀ x ∈ W, dist (h (Q x)) (h x) < ε := by
    intro x hx
    have hdisp : dist (H (τ x)) (τ x) ≤ c := by
      have hbound := dist_collarInwardMap_le (g := g) a (x := τ x) (hgpos (τ x).1)
      rw [hHdef]
      simpa only [hgdef] using hbound
    have hlt : dist (H (τ x)) (τ x) < δ := lt_of_le_of_lt hdisp (by rw [hcdef]; linarith)
    have hmain := hclose (H (τ x)) (hHU (hτ hx)) (τ x) (hτ hx) hlt
    rwa [hright hx] at hmain
  let f := W.piecewise Q id
  let f' := W.piecewise Q' id
  have hfW : EqOn f Q W := W.piecewise_eqOn Q id
  have hf'W : EqOn f' Q' W := W.piecewise_eqOn Q' id
  have hfR : EqOn f id R := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hfW hxW]
      exact hQR ⟨hxW, hx⟩
    · exact piecewise_eq_of_notMem W Q id hxW
  have hf'R : EqOn f' id R := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hf'W hxW]
      exact hQ'R ⟨hxW, hx⟩
    · exact piecewise_eq_of_notMem W Q' id hxW
  have hfpl : IsPiecewiseAffineOn f (W ∪ R) :=
    hQpl.piecewise_of_isClosed hR.isPLHomeomorphOn_id.isPiecewiseAffineOn
      hW.isClosed hR.isClosed hQR
  have hf'pl : IsPiecewiseAffineOn f' (W ∪ R) :=
    hQ'pl.piecewise_of_isClosed hR.isPLHomeomorphOn_id.isPiecewiseAffineOn
      hW.isClosed hR.isClosed hQ'R
  have hfinj : InjOn f (W ∪ R) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hfW hx, hfW hy] at hxy
      exact hQinj hx hy hxy
    · rw [hfW hx, hfR hy] at hxy
      exact (hQpreR x hx (hxy.symm ▸ hy)).symm.trans hxy
    · rw [hfR hx, hfW hy] at hxy
      exact hxy.trans (hQpreR y hy (hxy ▸ hx))
    · simpa only [hfR hx, hfR hy, id_eq] using hxy
  have hfmap : MapsTo f (W ∪ R) (W ∪ R) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hfW hx]
      exact Or.inl (hQW hx)
    · rw [hfR hx]
      exact Or.inr hx
  have hf'map : MapsTo f' (W ∪ R) (W ∪ R) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hf'W hx]
      exact Or.inl (hQ'W hx)
    · rw [hf'R hx]
      exact Or.inr hx
  refine ⟨f, f', hfpl, hfinj, hfmap, ?_, hf'pl, hf'map, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [hfW hx]
      exact hQnotB x hx
    · rw [hfR hx]
      exact Set.disjoint_right.mp hBR hx
  · intro x hx
    rcases hx with hx | hx
    · rw [hfW hx, hf'W (hQW hx)]
      exact hQQ' x hx
    · by_cases hxW : x ∈ W
      · rw [hfW hxW, hf'W (hQW hxW)]
        exact hQQ' x hxW
      · have hfix : f x = x := hfR hx
        rw [hfix]
        exact hf'R hx
  · intro x hx
    rcases hx with hx | hx
    · rw [hfW hx]
      exact hQdist x hx
    · rw [hfR hx]
      simpa using hε

/-- **The controlled inward push of a finite combinatorial three-manifold with boundary.**

This is `IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward` with the fixed
subpolyhedron empty, strengthened by a tolerance and by a piecewise affine left inverse.  The
tolerance is measured after a continuous map `h` into a metric space, as in `Moise352`, where
the source carries no metric.

The push is a piecewise linear homeomorphism of `K.space` onto its image, the image misses the
boundary complex entirely, and `f'` inverts it on the nose. -/
theorem IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_inward_dist_lt
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {Z : Type*} [MetricSpace Z] {h : E → Z}
    (hh : ContinuousOn h K.space) {ψ : E → ℝ} (hψ : ContinuousOn ψ K.space)
    (hψpos : ∀ x ∈ K.space, 0 < ψ x) :
    ∃ f f' : E → E, IsPiecewiseAffineOn f K.space ∧ InjOn f K.space ∧
      MapsTo f K.space K.space ∧
      (∀ x ∈ K.space, f x ∉ (@boundaryComplex E _ _ (Classical.decEq _) 3 K).space) ∧
      IsPiecewiseAffineOn f' K.space ∧ MapsTo f' K.space K.space ∧
      LeftInvOn f' f K.space ∧ ∀ x ∈ K.space, dist (h (f x)) (h x) < ψ x := by
  classical
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB := (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  obtain ⟨W, ρ, R, hW, hWK, hρ, hbottom, -, -, hRfinite, -, hRspace, -, -⟩ :=
    hK.exists_isPLHomeomorphOn_surface_prod_Icc K B hB Subset.rfl
      (a := 0) (b := 1) (by norm_num)
  let _ : Finite R.faces := hRfinite.to_subtype
  have hnhds := hρ.mem_nhdsSetWithin_boundaryComplex K hK (by norm_num) hWK hbottom
  obtain ⟨O, hO, hBO, hOW⟩ := mem_nhdsSetWithin.mp hnhds
  have hKR : K.space \ W ⊆ Oᶜ := by
    rintro x ⟨hxK, hxW⟩ hxO
    exact hxW (hOW ⟨hxO, hxK⟩)
  have hRO : R.space ⊆ Oᶜ := by
    rw [hRspace]
    exact closure_minimal hKR hO.isClosed_compl
  have hBR : Disjoint B.space R.space :=
    Set.disjoint_left.mpr fun x hxB hxR => hRO hxR (hBO hxB)
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hcover : W ∪ R.space = K.space := by
    apply Subset.antisymm (union_subset hWK hRK)
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (hRspace.symm ▸ subset_closure ⟨hx, hxW⟩)
  obtain ⟨ε, hε, hεle⟩ :=
    exists_pos_forall_le_of_continuousOn
      (DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace K) hψ hψpos
  obtain ⟨f, f', hfpl, hfinj, hfmap, hfB, hf'pl, hf'map, hinv, hdist⟩ :=
    hρ.exists_piecewiseAffineOn_inward_leftInvOn hW (isPolyhedron_space R) hBR
      (isPolyhedron_space B).isCompact hbottom (hh.mono hWK) hε
  rw [hcover] at hfpl hfinj hfmap hfB hf'pl hf'map hinv hdist
  exact ⟨f, f', hfpl, hfinj, hfmap, hfB, hf'pl, hf'map, hinv,
    fun x hx => lt_of_lt_of_le (hdist x hx) (hεle x hx)⟩

end Inward

section Manifold

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]

/-- **The controlled inward push of a compact polyhedral three-manifold with boundary inside a
piecewise linear three-manifold.**

The conclusion is the conclusion of `Moise352InwardPush 3` verbatim, and the hypotheses are
those of `Moise352InwardPush 3` with `K` compact, the embedding hypothesis on `h` weakened to
continuity on `K`.

The proof transports the controlled push of the presenting complex along the presenting piece.
The three transports are
`PLPieceIn.isPLOn_comp` and `PLPieceIn.isPLOn_of_eqOn_comp_invFunOn` for piecewise linearity,
`PLPieceIn.mem_interior_iff_not_mem_boundaryComplex_space` for the interior clause, and
`IsPLOn.mono_of_isOpen` to restrict the inverse to the open set `interior K`, which is legal
precisely because that set is open.

The open set `W` may be taken to be `interior K` itself; the push moves `K` into it because
the complex-level push misses the boundary complex. -/
theorem IsPolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt
    {K : Set M₁} (hK : IsPolyhedralManifoldWithBoundary (n := 3) 3 K) {h : M₁ → M₂}
    (hh : ContinuousOn h K) {ψ : M₁ → ℝ} (hψ : ContinuousOn ψ K)
    (hψpos : ∀ x ∈ K, 0 < ψ x) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn 3 3 p K ∧ InjOn p K ∧ IsPLOn 3 3 q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x := by
  classical
  obtain ⟨T, hT⟩ := hK
  have _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hbij : BijOn T.piece.map T.piece.complex.space K := T.piece.bijOn
  have hinv : MapsTo (Function.invFunOn T.piece.map T.piece.complex.space) K
      T.piece.complex.space := fun _ hy => hbij.surjOn.mapsTo_invFunOn hy
  have hleft : LeftInvOn (Function.invFunOn T.piece.map T.piece.complex.space) T.piece.map
      T.piece.complex.space := hbij.invOn_invFunOn.1
  have hright : RightInvOn (Function.invFunOn T.piece.map T.piece.complex.space) T.piece.map K :=
    hbij.invOn_invFunOn.2
  have hhS : ContinuousOn (fun y => h (T.piece.map y)) T.piece.complex.space :=
    hh.comp T.piece.continuousOn hbij.mapsTo
  have hψS : ContinuousOn (fun y => ψ (T.piece.map y)) T.piece.complex.space :=
    hψ.comp T.piece.continuousOn hbij.mapsTo
  have hψSpos : ∀ y ∈ T.piece.complex.space, 0 < ψ (T.piece.map y) :=
    fun y hy => hψpos _ (hbij.mapsTo hy)
  obtain ⟨f, f', hfpl, hfinj, hfmap, hfB, hf'pl, hf'map, hfinv, hfdist⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_inward_dist_lt
      T.piece.complex hT hhS hψS hψSpos
  have hPL : ∀ F : EuclideanSpace ℝ (Fin T.ambientDim) →
        EuclideanSpace ℝ (Fin T.ambientDim),
      IsPiecewiseAffineOn F T.piece.complex.space →
      MapsTo F T.piece.complex.space T.piece.complex.space →
      IsPLOn 3 3 (fun x => T.piece.map (F (Function.invFunOn T.piece.map
        T.piece.complex.space x))) K := by
    intro F hFpl hFmap
    refine T.piece.isPLOn_of_eqOn_comp_invFunOn (w := fun y => T.piece.map (F y)) ?_
      (fun _ _ => rfl)
    exact T.piece.isPLOn_comp hFpl hFmap
  refine ⟨fun x => T.piece.map (f (Function.invFunOn T.piece.map T.piece.complex.space x)),
    fun x => T.piece.map (f' (Function.invFunOn T.piece.map T.piece.complex.space x)),
    interior K, isOpen_interior, Subset.rfl, ?_, hPL f hfpl hfmap, ?_,
    (hPL f' hf'pl hf'map).mono_of_isOpen isOpen_interior interior_subset, ?_, ?_, ?_⟩
  · intro x hx
    exact (T.piece.mem_interior_iff_not_mem_boundaryComplex_space hT
      (hfmap (hinv hx))).mpr (hfB _ (hinv hx))
  · intro x hx y hy hxy
    have hfx := hfmap (hinv hx)
    have hfy := hfmap (hinv hy)
    have hstep : f (Function.invFunOn T.piece.map T.piece.complex.space x) =
        f (Function.invFunOn T.piece.map T.piece.complex.space y) :=
      hbij.injOn hfx hfy hxy
    have hbase := hfinj (hinv hx) (hinv hy) hstep
    rw [← hright hx, ← hright hy, hbase]
  · intro x hx
    exact hbij.mapsTo (hf'map (hinv (interior_subset hx)))
  · intro x hx
    have hfx := hfmap (hinv hx)
    have hstep : Function.invFunOn T.piece.map T.piece.complex.space
        (T.piece.map (f (Function.invFunOn T.piece.map T.piece.complex.space x))) =
        f (Function.invFunOn T.piece.map T.piece.complex.space x) := hleft hfx
    change T.piece.map (f' (Function.invFunOn T.piece.map T.piece.complex.space
      (T.piece.map (f (Function.invFunOn T.piece.map T.piece.complex.space x))))) = x
    rw [hstep, hfinv (hinv hx)]
    exact hright hx
  · intro x hx
    have hmain := hfdist _ (hinv hx)
    rwa [hright hx] at hmain

end Manifold

section Witness

/-- **A nondegenerate instance of the hypotheses of the inward push.**

The triangulated three-simplex is a compact polyhedral three-manifold with boundary inside the
model space, and its frontier is nonempty, so it exercises the content of the push: the
boundaryless witness `exists_isPLOn_injOn_leftInvOn_of_isOpen` does not. -/
theorem exists_isPolyhedralManifoldWithBoundary_frontier_nonempty :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsPolyhedralManifoldWithBoundary (n := 3) 3 K ∧ (frontier K).Nonempty := by
  classical
  obtain ⟨S, v, hfin, hman, hvert, -, -, -, -⟩ :=
    exists_simplicialArc_one_with_interior_edge (E := EuclideanSpace ℝ (Fin 3))
      (finrank_euclideanSpace_fin)
  have _ : Finite S.faces := hfin.to_subtype
  set e := chartAt (EuclideanSpace ℝ (Fin 3)) (0 : EuclideanSpace ℝ (Fin 3)) with he
  have hetarget : S.space ⊆ e.target := by
    rw [he, chartAt_self_eq]
    exact fun _ _ => trivial
  have himage : e.symm '' S.space = S.space := by
    rw [he, chartAt_self_eq]
    exact image_id _
  have hpm : IsPolyhedralManifoldWithBoundary (n := 3) 3 (e.symm '' S.space) :=
    ⟨⟨3, chartPieceOfComplex e (chart_mem_atlas _ _) S hetarget⟩, hman⟩
  rw [himage] at hpm
  refine ⟨S.space, hpm, ?_⟩
  have hne : S.space.Nonempty :=
    ⟨v 0, S.convexHull_subset_space (hvert 0 (by norm_num))
      (subset_convexHull ℝ _ (Finset.mem_singleton_self (v 0)))⟩
  rw [nonempty_iff_ne_empty]
  intro hfr
  rcases isClopen_iff.mp (isClopen_iff_frontier_eq_empty.mpr hfr) with hempty | huniv
  · exact (nonempty_iff_ne_empty.mp hne) hempty
  · exact noncompact_univ (EuclideanSpace ℝ (Fin 3))
      (huniv ▸ DifferentialGeometry.Topology.SimplicialComplex.isCompact_geometricSpace S)

/-- **The inward push, instantiated at a set with nonempty frontier.**

The conclusion is the conclusion of `Moise352InwardPush 3` for the identity embedding, at a
compact polyhedral three-manifold with boundary whose frontier is nonempty and at an arbitrary
continuous positive tolerance.  With `h` the identity the closeness clause reads
`dist (p x) x < ψ x`, which is Moise's "as close to the identity as we please". -/
theorem exists_frontier_nonempty_forall_exists_isPLOn_injOn_leftInvOn_dist_lt :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)), (frontier K).Nonempty ∧
      ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, ContinuousOn ψ K → (∀ x ∈ K, 0 < ψ x) →
      ∃ p q : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
          IsPLOn 3 3 p K ∧ InjOn p K ∧ IsPLOn 3 3 q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
          ∀ x ∈ K, dist (p x) x < ψ x := by
  obtain ⟨K, hK, hfr⟩ := exists_isPolyhedralManifoldWithBoundary_frontier_nonempty
  refine ⟨K, hfr, fun ψ hψ hψpos => ?_⟩
  obtain ⟨p, q, W, hW, hWK, hpW, hppl, hpinj, hqpl, hqK, hinv, hdist⟩ :=
    hK.exists_isPLOn_injOn_leftInvOn_dist_lt (h := id) continuousOn_id hψ hψpos
  exact ⟨p, q, W, hW, hWK, hpW, hppl, hpinj, hqpl, hqK, hinv, hdist⟩

end Witness

/-!
## What remains for `Moise352InwardPush`

The statement of `Moise352InwardPush 3` asks for the push on a *locally finite* polyhedral
three-manifold with boundary, not on a compact one.  Every step of the argument above except
one is already insensitive to compactness; the exception is the collar.

`IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_surface_prod_Icc` produces a
collar of the boundary of a **finite** complex in a normed space, and the tree has no collar
of the polyhedral boundary of a polyhedral manifold with boundary inside a piecewise linear
manifold at all: every collar in the tree lives in a normed space and needs a finite complex.
A locally finite polyhedral manifold with boundary is presented by a tower of compact pieces
whose own frontiers are interior to the manifold, so the pieces cannot be pushed one at a time
and glued: the stagewise gluing lemma
`LocallyFinitePieceTower.isPLOn_of_forall_eqOn_coreSpace` needs the stage maps to agree on the
earlier stages, and an inward push of a stage moves the earlier stage's frontier.

What has to be strengthened is therefore the collar, to the statement

    for a locally finite polyhedral `n`-manifold with boundary `K` inside a piecewise linear
    `n`-manifold `X` there are an open `V ⊆ X` with `frontier K ⊆ V` and a piecewise linear
    homeomorphism of `frontier K × [0,1]` onto `V ∩ K` which is the identity on
    `frontier K × {0}`,

after which the argument above applies verbatim with the constant push height replaced by a
positive piecewise affine function on `frontier K`, small on each piece of the tower.  The
ingredients the tree already has for this are `IsPolyhedralManifoldWithBoundary.isTwoSided_frontier`
and `PLPieceIn.exists_bicollar`, but the latter needs the surface to be a *closed* polyhedral
manifold, and nothing in the tree proves that the frontier of a locally finite polyhedral
manifold with boundary is one.
-/



end DifferentialGeometry.Topology.PiecewiseLinear
