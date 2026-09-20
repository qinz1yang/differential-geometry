/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PrismDiskBoundary

/-!
# Pushing a piecewise linear two-disk off itself

This file supplies the push-off step of the second closed case of Moise's Lemma 2. There an
innermost preimage curve bounds a clean disk, and the map is redefined on the disk bounded by
the paired curve using a second copy of that clean disk. Laying the second copy directly on
top of the retained one would produce a two dimensional coincidence set, so the copy must
first be pushed off the original.

Two forms of the push-off are proved, both for a piecewise linear two-disk `D` parametrized
by `r` on the standard two-simplex, with boundary circle `J = r '' stdSimplexBoundary 2`.

The first form assumes `D` lies inside a piecewise linear two-sphere `S`. The parallel copy
is the complementary disk `closure (S \ D)`.

The second form, which is the one Moise's Lemma 2 uses, assumes a collar of `D`, that is a
piecewise linear homeomorphism `ρ` from the prism `D ×ˢ Icc a b` onto a set `C` with
`ρ (x, a) = x` on `D`. The parallel copy is the image under `ρ` of the top face `D ×ˢ {b}`
together with the side wall `J ×ˢ Icc a b` over the boundary circle.

In both cases the copy `D'` is again a piecewise linear two-ball, it is parametrized by a map
whose boundary circle is exactly the boundary circle `J` of `D`, and `D' ∩ D = J`. The last
conclusion is the one that the surgery consumes: the coincidence set of the pushed off copy
with the original is the shared boundary curve, a piecewise linear one-sphere, and not a two
dimensional overlap.

The push-off produced here has the same boundary circle as the original disk, and both disks
are piecewise linear two-balls, hence piecewise linear homeomorphic. No claim is made that
the resulting homeomorphism from `D` to `D'` restricts to the identity on `J`; fixing the
boundary pointwise would require an extension result for homeomorphisms of the circle, which
is not needed for the coincidence set statement.

The two auxiliary results about the top face and the side wall of a disk prism mirror the
bottom face statements `isPLBall_prism_bottom_union_side` and
`IsPLHomeomorphOn.image_stdSimplexBoundary_prism_bottom_union_side`.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The top face of the prism over a piecewise linear two-disk `D`, together with the side
wall over the boundary circle of `D`, is a piecewise linear two-ball. It is the closure of
the complement of the bottom face `D ×ˢ {a}` in the boundary sphere of the prism. -/
theorem IsPLHomeomorphOn.isPLBall_prism_top_union_side
    {D : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    {a b : ℝ} (hab : a < b) :
    IsPLBall 2 (D ×ˢ {b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b) := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hJD : r '' stdSimplexBoundary 2 ⊆ D :=
    (image_mono fun _ hx => hx.1).trans hr.image_eq.subset
  have hS : IsPLSphere 2 (D ×ˢ {a, b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b) :=
    hr.isPLSphere_prism_boundary hab
  have hbot : IsPLBall 2 (D ×ˢ ({a} : Set ℝ)) :=
    hD.of_isPLHomeomorphOn (hD.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hbotS : D ×ˢ ({a} : Set ℝ) ⊆ D ×ˢ {a, b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b :=
    fun _ hz => Or.inl ⟨hz.1, Or.inl hz.2⟩
  have hdiff : (D ×ˢ {a, b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b) \ D ×ˢ ({a} : Set ℝ) =
      D ×ˢ {b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Ioc a b := by
    ext z
    constructor
    · rintro ⟨⟨hzD, hza | hzb⟩ | ⟨hzJ, hza, hzb⟩, hznot⟩
      · exact (hznot ⟨hzD, hza⟩).elim
      · exact Or.inl ⟨hzD, hzb⟩
      · exact Or.inr ⟨hzJ, lt_of_le_of_ne hza fun heq => hznot ⟨hJD hzJ, heq.symm⟩, hzb⟩
    · rintro (⟨hzD, hzb⟩ | ⟨hzJ, hza, hzb⟩)
      · exact ⟨Or.inl ⟨hzD, Or.inr hzb⟩, fun hz => hab.ne (hz.2.symm.trans hzb)⟩
      · exact ⟨Or.inr ⟨hzJ, hza.le, hzb⟩, fun hz => hza.ne' hz.2⟩
  have h := hS.isPLBall_closure_sdiff hbot hbotS
  rw [hdiff, closure_union, closure_prod_eq, closure_prod_eq,
    hD.isPolyhedron.isClosed.closure_eq, isClosed_singleton.closure_eq,
    hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isClosed.closure_eq,
    closure_Ioc hab.ne] at h
  exact h

/-- The boundary circle of the top face together with the side wall of a disk prism is the
copy `J ×ˢ {a}` of the boundary circle `J` of the disk at the near end of the prism. This
mirrors `IsPLHomeomorphOn.image_stdSimplexBoundary_prism_bottom_union_side`. -/
theorem IsPLHomeomorphOn.image_stdSimplexBoundary_prism_top_union_side
    {D : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    {a b : ℝ} (hab : a < b) {q : (Fin 3 → ℝ) → E × ℝ}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3))
      (D ×ˢ {b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)) :
    q '' stdSimplexBoundary 2 = (r '' stdSimplexBoundary 2) ×ˢ {a} := by
  let J := r '' stdSimplexBoundary 2
  let S := D ×ˢ {a, b} ∪ J ×ˢ Icc a b
  let A := D ×ˢ {b} ∪ J ×ˢ Icc a b
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hr.image_eq.subset
  have hS : IsPLSphere 2 S := hr.isPLSphere_prism_boundary hab
  have hAS : A ⊆ S := union_subset
    (fun _ hx => Or.inl ⟨hx.1, Or.inr hx.2⟩) subset_union_right
  have hdiff : S \ A = (D \ J) ×ˢ {a} := by
    ext z
    constructor
    · rintro ⟨⟨hzD, hza | hzb⟩ | hzside, hzA⟩
      · refine ⟨⟨hzD, fun hzJ => hzA (Or.inr ⟨hzJ, ?_⟩)⟩, hza⟩
        rw [show z.2 = a from hza]
        exact ⟨le_rfl, hab.le⟩
      · exact (hzA (Or.inl ⟨hzD, hzb⟩)).elim
      · exact (hzA (Or.inr hzside)).elim
    · rintro ⟨⟨hzD, hzJ⟩, hza⟩
      refine ⟨Or.inl ⟨hzD, Or.inl hza⟩, ?_⟩
      rintro (⟨_, hzb⟩ | ⟨hzJ', _⟩)
      · exact hab.ne (hza.symm.trans hzb)
      · exact hzJ hzJ'
  have hcl : closure (S \ A) = D ×ˢ ({a} : Set ℝ) := by
    rw [hdiff, closure_prod_eq, hr.closure_sdiff_image_stdSimplexBoundary,
      isClosed_singleton.closure_eq]
  have hmeet : A ∩ D ×ˢ ({a} : Set ℝ) = J ×ˢ {a} := by
    ext z
    constructor
    · rintro ⟨hztop | hzside, hz⟩
      · exact (hab.ne (hz.2.symm.trans hztop.2)).elim
      · exact ⟨hzside.1, hz.2⟩
    · rintro ⟨hzJ, hza⟩
      refine ⟨Or.inr ⟨hzJ, ?_⟩, hJD hzJ, hza⟩
      rw [show z.2 = a from hza]
      exact ⟨le_rfl, hab.le⟩
  have h := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hAS
  rw [hcl, hmeet] at h
  exact h.symm

/-- **Push-off across a two-sphere.** A piecewise linear two-disk `D` lying in a piecewise
linear two-sphere `S` has a parallel copy inside `S`, namely the complementary disk
`closure (S \ D)`. The copy is a piecewise linear two-ball, its boundary circle is the
boundary circle of `D`, and it meets `D` exactly in that circle. -/
theorem IsPLSphere.exists_isPLHomeomorphOn_pushOff_disk {S D : Set E} (hS : IsPLSphere 2 S)
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) (hDS : D ⊆ S) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D' ∧ D' ⊆ S ∧
        q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
          D' ∩ D = r '' stdSimplexBoundary 2 := by
  obtain ⟨q, hq⟩ := hS.isPLBall_closure_sdiff ⟨r, hr⟩ hDS
  have hmeet : closure (S \ D) ∩ D = r '' stdSimplexBoundary 2 := by
    rw [inter_comm]
    exact hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hDS
  exact ⟨closure (S \ D), q, hq, closure_minimal sdiff_subset hS.isPolyhedron.isClosed,
    (hS.image_stdSimplexBoundary_complement ⟨r, hr⟩ hDS hq).trans hmeet, hmeet⟩

/-- **Push-off along a collar.** Let `D` be a piecewise linear two-disk parametrized by `r`,
with boundary circle `J = r '' stdSimplexBoundary 2`, and let `ρ` be a collar of `D`, that is
a piecewise linear homeomorphism of the prism `D ×ˢ Icc a b` onto `C` which is the identity
on the near face, `ρ (x, a) = x` for `x ∈ D`.

Then there is a parallel copy `D' ⊆ C` of `D`: a piecewise linear two-ball, parametrized by
a map whose boundary circle is exactly `J`, and meeting `D` exactly in `J`. Concretely `D'`
is the image under `ρ` of the far face `D ×ˢ {b}` together with the side wall `J ×ˢ Icc a b`.

The hypotheses are one sided: only a collar of `D` is required, not a bicollar, and `D` need
not be two sided in an ambient manifold. No ambient manifold or dimension assumption is made
on `E` beyond finite dimensionality; the ambient hypotheses enter only through the collar. -/
theorem IsPLHomeomorphOn.exists_isPLHomeomorphOn_pushOff_of_collar {D C : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) {a b : ℝ}
    (hab : a < b) {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (D ×ˢ Icc a b) C)
    (hbase : ∀ x ∈ D, ρ (x, a) = x) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D' ∧ D' ⊆ C ∧
        q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
          D' ∩ D = r '' stdSimplexBoundary 2 := by
  have hJD : r '' stdSimplexBoundary 2 ⊆ D :=
    (image_mono fun _ hx => hx.1).trans hr.image_eq.subset
  have hM : IsPLBall 2 (D ×ˢ {b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b) :=
    hr.isPLBall_prism_top_union_side hab
  have hMsub : D ×ˢ {b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b ⊆ D ×ˢ Icc a b := by
    refine union_subset (fun z hz => ⟨hz.1, ?_⟩) fun z hz => ⟨hJD hz.1, hz.2⟩
    have hzb : z.2 = b := hz.2
    exact ⟨hab.le.trans hzb.ge, hzb.le⟩
  have hMpoly : IsPolyhedron (D ×ˢ {b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b) :=
    hM.isPolyhedron
  obtain ⟨p, hp⟩ := hM
  have hpb := hr.image_stdSimplexBoundary_prism_top_union_side hab hp
  refine ⟨ρ '' (D ×ˢ {b} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b), ρ ∘ p,
    hp.trans (hρ.restrict hMpoly hMsub), (image_mono hMsub).trans hρ.image_eq.subset, ?_, ?_⟩
  · rw [image_comp, hpb]
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨u, t⟩ := z
      have ht : t = a := hz.2
      subst ht
      rw [hbase u (hJD hz.1)]
      exact hz.1
    · intro x hx
      exact ⟨(x, a), ⟨hx, rfl⟩, hbase x (hJD hx)⟩
  · apply Subset.antisymm
    · rintro y ⟨⟨z, hzM, rfl⟩, hyD⟩
      have hzeq : z = (ρ z, a) :=
        hρ.bijOn.injOn (hMsub hzM) ⟨hyD, le_rfl, hab.le⟩ (hbase (ρ z) hyD).symm
      rcases hzM with htop | hside
      · exact absurd ((congrArg Prod.snd hzeq).symm.trans htop.2) hab.ne
      · have hz1 : z.1 ∈ r '' stdSimplexBoundary 2 := hside.1
        rwa [congrArg Prod.fst hzeq] at hz1
    · intro x hx
      exact ⟨⟨(x, a), Or.inr ⟨hx, le_rfl, hab.le⟩, hbase x (hJD hx)⟩, hJD hx⟩

/-- The consequence of the push-off that Moise's Lemma 2 consumes. A piecewise linear
two-disk with a collar has a parallel copy inside the collar whose coincidence set with the
original is a piecewise linear one-sphere, the shared boundary circle, and which is disjoint
from the original away from that circle. In particular the coincidence set is one
dimensional, so the copy together with the original is not a two dimensional overlap. -/
theorem IsPLHomeomorphOn.exists_isPLSphere_inter_pushOff_of_collar {D C : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) {a b : ℝ}
    (hab : a < b) {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (D ×ˢ Icc a b) C)
    (hbase : ∀ x ∈ D, ρ (x, a) = x) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D' ∧ D' ⊆ C ∧
        q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
          IsPLSphere 1 (D' ∩ D) ∧ Disjoint (D' \ r '' stdSimplexBoundary 2) D := by
  obtain ⟨D', q, hq, hDC, hbd, hmeet⟩ :=
    hr.exists_isPLHomeomorphOn_pushOff_of_collar hab hρ hbase
  refine ⟨D', q, hq, hDC, hbd, ?_, ?_⟩
  · rw [hmeet]
    exact hr.isPLSphere_image_stdSimplexBoundary
  · rw [Set.disjoint_left]
    rintro x ⟨hxD', hxJ⟩ hxD
    exact hxJ (hmeet.subset ⟨hxD', hxD⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
