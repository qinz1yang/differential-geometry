/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.InwardPushComposition

/-!
# The limit of a stagewise family of inward pushes

`InwardPushComposition.lean` composes two inward pushes of the same locally finite polyhedral
manifold with boundary `K`.  Both of its factors are asked to map `K` into `interior K`, which
is what lets `IsPLOn.comp_of_isOpen` be applied, and which a *stage* push does not satisfy: a
stage push moves one compact part of `K \ interior K` inward and is the identity near the rest
of the relative boundary, so its image meets `K \ interior K` and no open set carries it.

Two things are supplied here.

The first is the composition rule that a stagewise construction actually needs,
`IsPLWithinAt.comp` and `IsPLOn.comp_of_mapsTo`: piecewise linearity of `g ∘ f` on `s` from
piecewise linearity of `f` on `s`, of `g` on `t`, and `MapsTo f s t`, with no openness anywhere.
The proof shrinks `s` to `s ∩ f ⁻¹' e'.source` for the chart `e'` at `f x`, which is a
neighbourhood of `x` within `s` by continuity, and on which the chart round trip
`e'.symm ∘ e'` is the identity, so that the composite of the two coordinate representations is
literally the coordinate representation of the composite.

The second is the passage to the limit.  A stagewise construction produces compact stages
`N i` exhausting `K`, accumulated pushes `P i = p i ∘ ⋯ ∘ p 0` with inverses `Q i`, and open
sets `G i ⊆ interior K` holding the moved stage `P i '' N i`.  What makes the family converge
is not local finiteness of the collars — every collar of a later stage still surrounds the whole
relative boundary — but the requirement that each stage push be the identity on the compact
region already moved inward, which gives the two stabilisation clauses
`EqOn (P j) (P i) (N i)` and `EqOn (Q j) (Q i) (G i)` for `i ≤ j`.  The limit is then the glued
map, and the open set of the conclusion is `⋃ i, G i`; the intersection `⋂ i, W i` of the
collars, which is what a naive limit would produce, is not open and is not used.

## Main results

* `IsPLWithinAt.comp`, `IsPLOn.comp_of_mapsTo`: composition of piecewise linear maps along a
  `MapsTo` hypothesis, between manifolds and with no openness assumption.
* `exists_forall_eqOn_of_forall_le`: a family of maps agreeing with all its predecessors on the
  stages is glued into a single map.
* `exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages`: the conclusion of `Moise352InwardPush n`
  for a given glued pair `p`, `q`.
* `exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family`: the same from the stagewise data
  alone, the glued pair being produced by `exists_forall_eqOn_of_forall_le`.
* `exists_isPLOn_injOn_leftInvOn_dist_lt_of_one_stage`: the compact push of
  `IsPolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt` recovered from the
  stage family at the constant family.  This is the consistency check on the limit: the
  constant family is admissible, and by
  `exists_isPolyhedralManifoldWithBoundary_frontier_nonempty` it occurs at sets with nonempty
  frontier, so the limit statement is not satisfied only by the boundaryless witness of
  `SkeletonReduction.lean`.

## What remains

Only the stage push itself.  A construction of maps `p i`, `q i` which are the identity on a
prescribed compact subset of `interior K`, move a prescribed compact subset of
`K \ interior K` into `interior K`, and stay within a prescribed tolerance, feeds
`exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family` through `IsPLOn.comp_of_mapsTo` and
yields `Moise352InwardPush n`.  Nothing in this file is specific to dimension three.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Composition

variable {n m p : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]

/-- **Composition of piecewise linear maps along a `MapsTo` hypothesis.**

`IsPLAt.comp_isPLWithinAt` needs the outer map to be piecewise linear at the image point, that
is on a whole neighbourhood of it, and `IsPLOn.comp_of_isOpen` needs it to be piecewise linear
on an open set containing the image.  Neither is available when both maps are piecewise linear
on the same set with boundary.  Here the outer map is only asked to be piecewise linear within
the set `t` into which the inner map sends `s`.

Piecewise linearity within a set is not monotone in the set, so the set has first to be cut down
to `s ∩ f ⁻¹' e'.source`, a neighbourhood of `x` within `s`: there the chart `e'` at `f x` is
invertible at every image point, which is what identifies the composite of the two coordinate
representations with the coordinate representation of the composite. -/
theorem IsPLWithinAt.comp {f : M → N} {g : N → P} {s : Set M} {t : Set N} {x : M}
    (hg : IsPLWithinAt m p g t (f x)) (hf : IsPLWithinAt n m f s x) (hst : MapsTo f s t) :
    IsPLWithinAt n p (g ∘ f) s x := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e' := chartAt (EuclideanSpace ℝ (Fin m)) (f x)
  let e'' := chartAt (EuclideanSpace ℝ (Fin p)) (g (f x))
  have hx : x ∈ e.source := mem_chart_source _ _
  have hfx : f x ∈ e'.source := mem_chart_source _ _
  have hpre : f ⁻¹' e'.source ∈ 𝓝[s] x :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hfx)
  refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hpre).mp ?_
  have hsub : s ∩ f ⁻¹' e'.source ⊆ s := inter_subset_left
  have hnb : s ∩ f ⁻¹' e'.source ∈ 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin hpre
  have hf' : IsPLWithinAt n m f (s ∩ f ⁻¹' e'.source) x := hf.mono_of_mem_nhdsWithin hsub hnb
  refine ⟨hg.continuousWithinAt.comp hf'.continuousWithinAt (hst.mono_left hsub), ?_⟩
  have hgcoord : IsPiecewiseAffineWithinAt (e'' ∘ g ∘ e'.symm) (e'.symm ⁻¹' t) (e' (f x)) :=
    hg.prop
  have hpoint : (e' ∘ f ∘ e.symm) (e x) = e' (f x) := by
    change e' (f (e.symm (e x))) = e' (f x)
    rw [e.left_inv hx]
  rw [← hpoint] at hgcoord
  have hcomp := hgcoord.comp hf'.prop
  have hset : e.symm ⁻¹' (s ∩ f ⁻¹' e'.source) ∩
      (e' ∘ f ∘ e.symm) ⁻¹' (e'.symm ⁻¹' t) = e.symm ⁻¹' (s ∩ f ⁻¹' e'.source) := by
    refine inter_eq_left.mpr fun z hz => ?_
    change e'.symm (e' (f (e.symm z))) ∈ t
    rw [e'.left_inv hz.2]
    exact hst hz.1
  rw [hset] at hcomp
  refine piecewiseAffineProperty_localInvariantProp.congr_nhdsWithin ?_ ?_ hcomp
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change e'' (g (e'.symm (e' (f (e.symm z))))) = e'' (g (f (e.symm z)))
    rw [e'.left_inv hz.2]
  · change e'' (g (e'.symm (e' (f (e.symm (e x)))))) = e'' (g (f (e.symm (e x))))
    rw [e.left_inv hx, e'.left_inv hfx]

/-- **Composition of piecewise linear maps on sets**, the pointwise form of
`IsPLWithinAt.comp`.  No set is required to be open, and the two sets live in different
manifolds. -/
theorem IsPLOn.comp_of_mapsTo {f : M → N} {g : N → P} {s : Set M} {t : Set N}
    (hg : IsPLOn m p g t) (hf : IsPLOn n m f s) (hst : MapsTo f s t) : IsPLOn n p (g ∘ f) s :=
  fun x hx => IsPLWithinAt.comp (hg (f x) (hst hx)) (hf x hx) hst

end Composition

section Glue

variable {X Y : Type*}

/-- **Gluing a stagewise family of maps.**

Each member of the family has to agree with *all* of its predecessors on the corresponding
stage, not only with the immediately preceding one; this is what a composite of stage pushes
delivers, since a push fixes pointwise everything the earlier stages have already moved.  The
glued map is the value at the least stage containing the point, and it agrees with every
member of the family on that member's stage. -/
theorem exists_forall_eqOn_of_forall_le {A : ℕ → Set X} (F : ℕ → X → Y)
    (hF : ∀ i j, i ≤ j → EqOn (F j) (F i) (A i)) : ∃ G : X → Y, ∀ i, EqOn G (F i) (A i) := by
  classical
  refine ⟨fun x => if hx : ∃ i, x ∈ A i then F (Nat.find hx) x else F 0 x, fun i x hx => ?_⟩
  have hex : ∃ j, x ∈ A j := ⟨i, hx⟩
  simp only [dif_pos hex]
  exact (hF (Nat.find hex) i (Nat.find_min' hex hx) (Nat.find_spec hex)).symm

end Glue

section Stages

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [MetricSpace M₂]

/-- **The limit of a stagewise family of inward pushes**, for a given glued pair.

The hypotheses are the conclusion of `Moise352InwardPush n` stage by stage, together with the
two clauses that make the family converge: the glued push `p` agrees with `P i` on the stage
`N i`, and the glued inverse `q` agrees with `Q i` on the open set `G i` holding the moved
stage.  Both are supplied by `exists_forall_eqOn_of_forall_le` from the stabilisation clauses;
they are taken as hypotheses here so that no choice is hidden inside the statement.

The open set of the conclusion is `⋃ i, G i`.  Piecewise linearity of `p` on `K` is local: at a
point of `N i` the stage `N (i + 1)` is a neighbourhood within `K`, and `p` agrees with the
single map `P (i + 1)` on it.  Piecewise linearity of `q` on `⋃ i, G i` is local for the
cheaper reason that each `G i` is open.  Injectivity uses that the stages increase, so two
points of `K` lie in a common stage. -/
theorem exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages {K : Set M₁} {h : M₁ → M₂}
    {ψ : M₁ → ℝ} {N G : ℕ → Set M₁} {P Q : ℕ → M₁ → M₁} {p q : M₁ → M₁}
    (hNmono : Monotone N) (hNK : ∀ i, N i ⊆ K) (hNcover : ∀ x ∈ K, ∃ i, x ∈ N i)
    (hNnhds : ∀ i, ∀ x ∈ N i, N (i + 1) ∈ 𝓝[K] x) (hGopen : ∀ i, IsOpen (G i))
    (hGint : ∀ i, G i ⊆ interior K) (hPG : ∀ i, MapsTo (P i) (N i) (G i))
    (hPpl : ∀ i, IsPLOn n n (P i) K) (hPinj : ∀ i, InjOn (P i) K)
    (hQpl : ∀ i, IsPLOn n n (Q i) (G i)) (hQK : ∀ i, MapsTo (Q i) (G i) K)
    (hQP : ∀ i, LeftInvOn (Q i) (P i) K)
    (hdist : ∀ i, ∀ x ∈ N i, dist (h (P i x)) (h x) < ψ x)
    (hp : ∀ i, EqOn p (P i) (N i)) (hq : ∀ i, EqOn q (Q i) (G i)) :
    ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x := by
  refine ⟨⋃ i, G i, isOpen_iUnion hGopen, iUnion_subset hGint, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [hp i hi]
    exact hPG i hi
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    have hmem : x ∈ N (i + 1) := hNmono (Nat.le_succ i) hi
    have hnb : N (i + 1) ∈ 𝓝[K] x := hNnhds i x hi
    have hbase : IsPLWithinAt n n (P (i + 1)) (N (i + 1)) x :=
      IsPLWithinAt.mono_of_mem_nhdsWithin (hPpl (i + 1) x hx) (hNK (i + 1)) hnb
    have hcongr : IsPLWithinAt n n p (N (i + 1)) x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem hbase
        (fun y hy => hp (i + 1) hy) hmem
    refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hnb).mp ?_
    rw [inter_eq_right.mpr (hNK (i + 1))]
    exact hcongr
  · intro x hx y hy hxy
    obtain ⟨i, hi⟩ := hNcover x hx
    obtain ⟨j, hj⟩ := hNcover y hy
    have hi' : x ∈ N (max i j) := hNmono (le_max_left i j) hi
    have hj' : y ∈ N (max i j) := hNmono (le_max_right i j) hj
    refine hPinj (max i j) hx hy ?_
    rw [← hp (max i j) hi', ← hp (max i j) hj']
    exact hxy
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hcongr : IsPLWithinAt n n q (G i) y :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem (hQpl i y hi)
        (fun z hz => hq i hz) hi
    have hset : (fun z => z ∈ G i) =ᶠ[𝓝 y] (fun z => z ∈ ⋃ j, G j) := by
      filter_upwards [(hGopen i).mem_nhds hi] with z hz
      apply propext
      exact ⟨fun _ => mem_iUnion.mpr ⟨i, hz⟩, fun _ => hz⟩
    exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hcongr
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    rw [hq i hi]
    exact hQK i hi
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    rw [hp i hi, hq i (hPG i hi)]
    exact hQP i hx
  · intro x hx
    obtain ⟨i, hi⟩ := hNcover x hx
    rw [hp i hi]
    exact hdist i x hi

/-- **The limit of a stagewise family of inward pushes.**

This is `exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages` with the glued pair produced from the
stabilisation clauses `hPstab` and `hQstab`, and its conclusion is the conclusion of
`Moise352InwardPush n` for `K`.

The stabilisation clauses are exactly what a stage push delivers when it is required to be the
identity on the compact region already moved inward: the accumulated push `P j` differs from
`P i` only through the stages after `i`, and each of those fixes `P i '' N i` pointwise, while
the accumulated inverses fix `G i` for the same reason.  No agreement between consecutive stage
pushes themselves is asked for anywhere, and none is available: a stage push fixes its own seam,
so a family agreeing on the earlier stages would freeze the seam points in `K \ interior K`. -/
theorem exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family {K : Set M₁} {h : M₁ → M₂}
    {ψ : M₁ → ℝ} {N G : ℕ → Set M₁} {P Q : ℕ → M₁ → M₁}
    (hNmono : Monotone N) (hNK : ∀ i, N i ⊆ K) (hNcover : ∀ x ∈ K, ∃ i, x ∈ N i)
    (hNnhds : ∀ i, ∀ x ∈ N i, N (i + 1) ∈ 𝓝[K] x) (hGopen : ∀ i, IsOpen (G i))
    (hGint : ∀ i, G i ⊆ interior K) (hPG : ∀ i, MapsTo (P i) (N i) (G i))
    (hPpl : ∀ i, IsPLOn n n (P i) K) (hPinj : ∀ i, InjOn (P i) K)
    (hQpl : ∀ i, IsPLOn n n (Q i) (G i)) (hQK : ∀ i, MapsTo (Q i) (G i) K)
    (hQP : ∀ i, LeftInvOn (Q i) (P i) K)
    (hdist : ∀ i, ∀ x ∈ N i, dist (h (P i x)) (h x) < ψ x)
    (hPstab : ∀ i j, i ≤ j → EqOn (P j) (P i) (N i))
    (hQstab : ∀ i j, i ≤ j → EqOn (Q j) (Q i) (G i)) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn n n p K ∧ InjOn p K ∧ IsPLOn n n q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x := by
  obtain ⟨p, hp⟩ := exists_forall_eqOn_of_forall_le (A := N) P hPstab
  obtain ⟨q, hq⟩ := exists_forall_eqOn_of_forall_le (A := G) Q hQstab
  obtain ⟨W, hW⟩ := exists_isPLOn_injOn_leftInvOn_dist_lt_of_stages hNmono hNK hNcover hNnhds
    hGopen hGint hPG hPpl hPinj hQpl hQK hQP hdist hp hq
  exact ⟨p, q, W, hW⟩

end Stages

section Witness

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]

/-- **The compact inward push recovered from the stage family.**

The constant family, one stage equal to `K` and one open set equal to the `W` of
`IsPolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt`, satisfies every
hypothesis of `exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family`: a constant family is
monotone, `K` is a neighbourhood of each of its points within itself, and both stabilisation
clauses are reflexivity.

This is the consistency check on the limit.  By
`exists_isPolyhedralManifoldWithBoundary_frontier_nonempty` the compact hypothesis is met at
sets with nonempty frontier, so the limit statement is exercised at data where the push has to
move something, and not only at the boundaryless witness of `SkeletonReduction.lean`. -/
theorem exists_isPLOn_injOn_leftInvOn_dist_lt_of_one_stage {K : Set M₁}
    (hK : IsPolyhedralManifoldWithBoundary (n := 3) 3 K) {h : M₁ → M₂} (hh : ContinuousOn h K)
    {ψ : M₁ → ℝ} (hψ : ContinuousOn ψ K) (hψpos : ∀ x ∈ K, 0 < ψ x) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn 3 3 p K ∧ InjOn p K ∧ IsPLOn 3 3 q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x := by
  obtain ⟨p, q, W, hWopen, hWK, hpW, hppl, hpinj, hqpl, hqK, hinv, hpdist⟩ :=
    hK.exists_isPLOn_injOn_leftInvOn_dist_lt hh hψ hψpos
  exact exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family (N := fun _ => K)
    (G := fun _ => W) (P := fun _ => p) (Q := fun _ => q) monotone_const (fun _ => Subset.rfl)
    (fun x hx => ⟨0, hx⟩) (fun _ x _ => self_mem_nhdsWithin) (fun _ => hWopen) (fun _ => hWK)
    (fun _ => hpW) (fun _ => hppl) (fun _ => hpinj) (fun _ => hqpl) (fun _ => hqK)
    (fun _ => hinv) (fun _ x hx => hpdist x hx) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

end Witness

end DifferentialGeometry.Topology.PiecewiseLinear
