/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DiskPushOff

/-!
# Collars of piecewise linear two-disks that do not lie in the boundary

`IsCombinatorialManifoldWithBoundary.exists_collar_of_boundary_disk` collars a piecewise
linear two-disk lying in the boundary of a combinatorial three-manifold, and
`IsPLHomeomorphOn.exists_isPLHomeomorphOn_pushOff_of_collar` consumes such a collar to push
the disk off itself.  For a disk that does not lie in the boundary the bicollar producers of
this tree do not apply: `IsCombinatorialManifoldWithBoundary.exists_bicollar`,
`PLPieceIn.exists_bicollar` and `IsPolyhedralManifold.exists_bicollar` all assume the surface
is a *closed* combinatorial two-manifold which is two sided, and a two-disk is neither.

This file collars such a disk from the centered prism neighbourhoods of the spanning disk
layer.  A *centered prism* for a two-disk `D` parametrized by `r` on the standard two-simplex
is a piecewise linear homeomorphism `f` of `stdSimplex ℝ (Fin 3) ×ˢ Icc (-1) 1` onto a set `N`
with `f (x, 0) = r x`, that is a product neighbourhood of `D` having `D` as its central level.

Main results.

* `IsPLHomeomorphOn.exists_collar_of_centered_prism` turns a centered prism into a collar in
  exactly the shape the push-off consumes: a piecewise linear homeomorphism `ρ` of
  `D ×ˢ Icc 0 1` onto a subset of `N` which is the identity on `D ×ˢ {0}` and which leaves `D`
  at once.  It applies to any centered prism, however that prism was obtained; the two
  producers below are the two ways this tree currently has of obtaining one.
* `IsPLHomeomorphOn.centered_prism_neg` reflects a centered prism in its central level.  It is
  again a centered prism for the same disk, so the bridge applied to it produces the collar of
  the disk on the other side.  This is the one feature an interior disk has over a boundary
  disk, and it is the only sense in which two-sidedness is claimed anywhere below.
* `IsPLBall.exists_collar_of_properly_embedded_disk` and
  `IsPLBall.exists_pushOff_of_properly_embedded_disk` collar, and push off, a two-disk
  properly embedded in a piecewise linear three-ball, that is one meeting the boundary
  two-sphere of the ball exactly in its own boundary circle.
* `IsCombinatorialManifold.exists_collar_of_spanning_disk` and
  `IsCombinatorialManifold.exists_pushOff_of_spanning_disk` do the same for a disk spanning a
  closed connected surface `S` in an ambient space of dimension three, with the collar and the
  parallel copy confined to any prescribed open neighbourhood of the disk.

The two push-off endpoints are the form the second closed case of Moise's Lemma 2 consumes:
the parallel copy is again a piecewise linear two-ball, it has the same boundary circle as the
original disk, and it meets the original exactly in that circle, so the coincidence set is one
dimensional.

No statement here weakens the hypotheses of the prism layer it rests on.  In particular a
two-disk whose boundary circle lies in the interior of the three-manifold and on no closed
surface is still not collared: that case needs its own centered prism.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Collar from a centered prism.**  Let `D` be a piecewise linear two-disk parametrized by
`r` on the standard two-simplex and let `f` be a centered prism for it, that is a piecewise
linear homeomorphism of `stdSimplex ℝ (Fin 3) ×ˢ Icc (-1) 1` onto `N` with `f (x, 0) = r x`.

Then the upper half of the prism is a collar of `D` in the shape
`IsPLHomeomorphOn.exists_isPLHomeomorphOn_pushOff_of_collar` consumes: a piecewise linear
homeomorphism `ρ` of `D ×ˢ Icc 0 1` onto a subset `C ⊆ N` containing `D`, which restricts to
the identity on the near face and carries the rest of the prism off `D`.

Applying the same statement to the reflected prism of `IsPLHomeomorphOn.centered_prism_neg`
produces a collar on the other side of `D`. -/
theorem IsPLHomeomorphOn.exists_collar_of_centered_prism {D N : Set E}
    {r : (Fin 3 → ℝ) → E} {f : (Fin 3 → ℝ) × ℝ → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N)
    (hzero : ∀ x ∈ stdSimplex ℝ (Fin 3), f (x, 0) = r x) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc (0 : ℝ) 1) C ∧ C ⊆ N ∧ D ⊆ C ∧
        (∀ x ∈ D, ρ (x, 0) = x) ∧ MapsTo ρ (D ×ˢ Ioc (0 : ℝ) 1) (C \ D) := by
  have hsub : stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 ⊆
      stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl)
  have hpoly : IsPolyhedron (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) :=
    (isPLBall_stdSimplex 2).isPolyhedron.prod
      (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron
  have hfC : IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (f '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)) := hf.restrict hpoly hsub
  have hρ : IsPLHomeomorphOn
      (f ∘ Prod.map (Function.invFunOn r (stdSimplex ℝ (Fin 3))) (id : ℝ → ℝ))
      (D ×ˢ Icc (0 : ℝ) 1) (f '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)) :=
    (hr.symm.prodMap
      (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron.isPLHomeomorphOn_id).trans hfC
  have hbase : ∀ x ∈ D,
      (f ∘ Prod.map (Function.invFunOn r (stdSimplex ℝ (Fin 3))) (id : ℝ → ℝ)) (x, 0) = x := by
    intro x hx
    change f (Function.invFunOn r (stdSimplex ℝ (Fin 3)) x, (0 : ℝ)) = x
    rw [hzero _ (hr.symm.bijOn.mapsTo hx)]
    exact hr.bijOn.invOn_invFunOn.2 hx
  have hDC : D ⊆ f '' (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx
    rw [← hbase x hx]
    exact hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  refine ⟨_, _, hρ, (image_mono hsub).trans hf.image_eq.subset, hDC, hbase, ?_⟩
  rintro z ⟨hzD, hzpos, hzle⟩
  have hzdom : z ∈ D ×ˢ Icc (0 : ℝ) 1 := ⟨hzD, hzpos.le, hzle⟩
  refine ⟨hρ.bijOn.mapsTo hzdom, ?_⟩
  intro hmem
  have heq := hρ.bijOn.injOn hzdom ⟨hmem, le_rfl, zero_le_one⟩ (hbase _ hmem).symm
  exact (ne_of_gt hzpos) (congrArg Prod.snd heq)

/-- **Reflection of a centered prism.**  Reflecting a centered prism `f` for the disk
`D = r '' stdSimplex ℝ (Fin 3)` in its central level gives a centered prism for the same disk,
onto the same set `N`, which exchanges the two sides of `D`.

Feeding it to `IsPLHomeomorphOn.exists_collar_of_centered_prism` produces the collar of `D` on
the side opposite to the one that theorem produces from `f`. -/
theorem IsPLHomeomorphOn.centered_prism_neg {N : Set E} {r : (Fin 3 → ℝ) → E}
    {f : (Fin 3 → ℝ) × ℝ → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N)
    (hzero : ∀ x ∈ stdSimplex ℝ (Fin 3), f (x, 0) = r x) :
    IsPLHomeomorphOn (f ∘ Prod.map (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (fun t : ℝ => -t))
        (stdSimplex ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N ∧
      ∀ x ∈ stdSimplex ℝ (Fin 3),
        (f ∘ Prod.map (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (fun t : ℝ => -t)) (x, 0) = r x := by
  refine ⟨?_, ?_⟩
  · have hreflect : IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
      apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
        (isPiecewiseAffineOn_of_affine_of_isHPolytope
          (-LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap isHPolytope_Icc)
      refine ⟨?_, fun _ _ _ _ h => neg_injective h, ?_⟩
      · intro t ht
        change -1 ≤ -t ∧ -t ≤ 1
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      · intro t ht
        exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg t⟩
    exact ((isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id.prodMap hreflect).trans hf
  · intro x hx
    change f (x, -(0 : ℝ)) = r x
    rw [neg_zero]
    exact hzero x hx

/-- **Collar of a two-disk properly embedded in a three-ball.**  Let `K` be a piecewise linear
three-ball in an ambient space of dimension three and let `D` be a piecewise linear two-disk
inside `K` meeting the boundary two-sphere of `K` exactly in its own boundary circle.

Then `D` has a collar in `K`: a piecewise linear homeomorphism `ρ` of `D ×ˢ Icc 0 1` onto a
subset `C ⊆ K.space` containing `D`, restricting to the identity on `D ×ˢ {0}` and carrying
`D ×ˢ Ioc 0 1` into `C \ D`.  No hypothesis places `D` in the boundary of `K`. -/
theorem IsPLBall.exists_collar_of_properly_embedded_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    (hdim : Module.finrank ℝ E = 3) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hproper : D ∩ frontier K.space = r '' stdSimplexBoundary 2) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc (0 : ℝ) 1) C ∧ C ⊆ K.space ∧ D ⊆ C ∧
        (∀ x ∈ D, ρ (x, 0) = x) ∧ MapsTo ρ (D ×ˢ Ioc (0 : ℝ) 1) (C \ D) := by
  obtain ⟨N, f, hf, hNK, hzero, -, -⟩ :=
    hK.exists_centered_prism_subset_of_boundary_neighborhood K hdim hr hDK hproper
      (S := frontier K.space) inter_subset_left
      (mem_nhdsSetWithin.mpr ⟨univ, isOpen_univ, subset_univ _, inter_subset_right⟩)
  obtain ⟨C, ρ, hρ, hCN, hDC, hbase, hmaps⟩ := hr.exists_collar_of_centered_prism hf hzero
  exact ⟨C, ρ, hρ, hCN.trans hNK, hDC, hbase, hmaps⟩

/-- **Push-off of a two-disk properly embedded in a three-ball.**  Under the hypotheses of
`IsPLBall.exists_collar_of_properly_embedded_disk` the disk `D` has a parallel copy `D'`
inside `K`: a piecewise linear two-ball parametrized by a map whose boundary circle is exactly
the boundary circle of `D`, and meeting `D` exactly in that circle.

This is the conclusion the second closed case of Moise's Lemma 2 consumes: the coincidence set
of the copy with the original is a piecewise linear one-sphere, not a two dimensional
overlap. -/
theorem IsPLBall.exists_pushOff_of_properly_embedded_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    (hdim : Module.finrank ℝ E = 3) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hproper : D ∩ frontier K.space = r '' stdSimplexBoundary 2) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D' ∧ D' ⊆ K.space ∧
        q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
          D' ∩ D = r '' stdSimplexBoundary 2 := by
  obtain ⟨C, ρ, hρ, hCK, -, hbase, -⟩ :=
    hK.exists_collar_of_properly_embedded_disk K hdim hr hDK hproper
  obtain ⟨D', q, hq, hD'C, hqb, hmeet⟩ :=
    hr.exists_isPLHomeomorphOn_pushOff_of_collar (by norm_num : (0 : ℝ) < 1) hρ hbase
  exact ⟨D', q, hq, hD'C.trans hCK, hqb, hmeet⟩

/-- **Collar of a disk spanning a closed surface.**  Let `S` be a closed connected
combinatorial two-manifold in an ambient space of dimension three and let `D` be a piecewise
linear two-disk meeting `S` exactly in its own boundary circle.  Then `D` has a collar inside
any prescribed open set `U` containing `D`.

Again the disk does not lie in the boundary of anything: only its boundary circle is
constrained, and the collar is one sided, so no two-sidedness of `D` is used or produced. -/
theorem IsCombinatorialManifold.exists_collar_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc (0 : ℝ) 1) C ∧ C ⊆ U ∧ D ⊆ C ∧
        (∀ x ∈ D, ρ (x, 0) = x) ∧ MapsTo ρ (D ×ˢ Ioc (0 : ℝ) 1) (C \ D) := by
  obtain ⟨N, f, hf, hNU, hzero, -, -⟩ :=
    hS.exists_centered_prism_neighborhood_of_spanning_disk S hSc hdim hr hmeet hU hDU
  obtain ⟨C, ρ, hρ, hCN, hDC, hbase, hmaps⟩ := hr.exists_collar_of_centered_prism hf hzero
  exact ⟨C, ρ, hρ, hCN.trans hNU, hDC, hbase, hmaps⟩

/-- **Push-off of a disk spanning a closed surface.**  Under the hypotheses of
`IsCombinatorialManifold.exists_collar_of_spanning_disk` the disk `D` has a parallel copy `D'`
inside the prescribed open set `U`: a piecewise linear two-ball whose boundary circle is the
boundary circle of `D`, meeting `D` exactly in that circle. -/
theorem IsCombinatorialManifold.exists_pushOff_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D' ∧ D' ⊆ U ∧
        q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
          D' ∩ D = r '' stdSimplexBoundary 2 := by
  obtain ⟨C, ρ, hρ, hCU, -, hbase, -⟩ :=
    hS.exists_collar_of_spanning_disk S hSc hdim hr hmeet hU hDU
  obtain ⟨D', q, hq, hD'C, hqb, hmeetD⟩ :=
    hr.exists_isPLHomeomorphOn_pushOff_of_collar (by norm_num : (0 : ℝ) < 1) hρ hbase
  exact ⟨D', q, hq, hD'C.trans hCU, hqb, hmeetD⟩

end DifferentialGeometry.Topology.PiecewiseLinear
