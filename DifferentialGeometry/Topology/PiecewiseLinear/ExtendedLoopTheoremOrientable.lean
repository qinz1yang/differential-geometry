/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.ExtendedLoopTheoremStatement
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarComplementCollars
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarBoundaryLoop

/-!
# The orientable extended loop theorem from the boundary loop theorem

The assembly proves `Moise264Orientable` from `Moise252` and two open leaves. It inherits
orientability for the cut manifold using `IsOrientable.of_space_subset`, applies the boundary
loop theorem, and adds a half collar using `DiskBoundaryCollar`. The original unrestricted
`Moise264` remains open; intrinsic two-sidedness and orientability are explicit here. The
already proved Euclidean local essential-disk theorem is not replaced by this general chain.

`exists_bicollar_complement_with_boundary_collars`: a finite cut manifold and half collars
back to the original surface, including component retractions; topology lane, reviewed OK, OPEN.
`exists_nontrivial_boundary_loop_of_bicollar_complement`: a nontrivial kernel loop transfers
to a collar-end boundary component of the same cut manifold; topology lane, reviewed OK, OPEN.

Both statements are frozen after the first review and lead due diligence recorded in
`consult/AZ-orientable-extended-loop-first-review-digest.md`. No new hypotheses were added.
The second leaf must derive the intrinsic boundary decomposition of the same complement
from its own inputs and identify each collar-end component. It does not receive those
certificates from the first leaf. The surface-product boundary and component-identification
interfaces remain proof obligations; the auxiliary vector-space frontier is not substituted.

The first leaf contains no loop or disk. The second contains no embedded disk. Its remaining
geometric argument is the innermost-circle procedure of Moise Section 26.4, including the
nonseparating case. A component retraction in the first leaf is the inverse collar-end map
on one connected surface component, extended constantly across the other clopen components.
It does not assert essentialness of any loop or boundary circle.
The innermost-circle procedure must also exclude the disappearance of every intersection
circle: retraction of the resulting nullhomotopy inside the bicollar would contradict the
original nontrivial kernel element. Finite descent alone does not exclude that outcome.

Common fixture, UNTESTED in Lean: a triangulated three-ball containing a standard unknotted
polyhedral torus in its interior, with a bicollar of that torus and a meridian as kernel loop.
The same collar and complementary manifold serve both leaves. No fixture certification or
proof of either leaf is claimed. Empty surfaces have no basepoint for the kernel premise;
disconnected surfaces and nonseparating two-sided surfaces are retained in the statements.
Additional untested fixtures use two disjoint tori, or a fiber sphere with one local tube in
the orientable manifold `S² × S¹`, realized in a sufficiently large finite-dimensional space.
The latter has a connected complement; its two collar ends need not lie in different
components of the cut manifold. The Section 33 application bridge remains open.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with a zero-diagnostic
check and an axiom audit; statement byte-identical with the frozen leaf):
`exists_bicollar_complement_with_boundary_collars` (module `BicollarComplementCollars`), from the
existing componentwise `IsCombinatorialManifoldWithBoundary.exists_bicollar`, rescaled so that the
open band is relatively open in `K`, with the cut manifold from
`IsCombinatorialManifoldWithBoundary.complement`.  The verified toolkit for the remaining leaf
(product-triangulation boundaries, band openness, the push-to-ends map and the end retraction, all
for the given collar) is the real module `BicollarBands`; the leaf itself still needs the
transversality of a PL singular disk against the collar levels and the planar innermost-circle
induction.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with zero-diagnostic checks
and an axiom audit; statement byte-identical with the frozen leaf):
`exists_nontrivial_boundary_loop_of_bicollar_complement` (module `BicollarBoundaryLoop`, over the
bricks `PLLevelCircles` — outside finitely many values an interior level set of a PL function on
a planar polyhedron is a finite disjoint union of PL circles — and `JordanDiskPasting`, the
innermost-circle induction with thin connected outer collars).  Route by contradiction: a PL
disk fill of the kernel loop, two generic collar levels pulled back to disjoint circles, the
push-to-ends map, the pasting induction (end retraction on the `W` side, the assumed
injectivity on the `R` side), and projection to `L`.  With both leaves proved this file has no
`sorry` and was promoted from `Skeleton/` to a real module on 2026-09-22; `moise264_orientable`
is a real theorem conditional only on `Moise252`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem moise264_orientable (h252 : Moise252) : Moise264Orientable := by
  classical
  intro E _ _ _ K hKfin hK hKo L hLfin hL hLK htwo x g hg hgin
  let _ : Finite K.faces := hKfin
  let _ : Finite L.faces := hLfin
  obtain ⟨W, ρ, R, hRfin, hρ, hρzero, hW, hWnhds, hR, hRspace, hRK, hRL,
      hboundary, _, hcollars⟩ :=
    exists_bicollar_complement_with_boundary_collars K L hK hL hLK htwo
  let _ : Finite R.faces := hRfin
  have hRo : IsOrientable 3 R := hKo.of_space_subset K R hRK hK hR
  obtain ⟨c, hcW, hsub, γ, hγR, hγ⟩ :=
    exists_nontrivial_boundary_loop_of_bicollar_complement K L R hK hL hLK hR
      W ρ hρ hρzero hW hWnhds hRspace x g hg hgin
  obtain ⟨D, r, hr, hDR, hDr, hb, hessential⟩ :=
    h252 R hRfin hR hRo c hsub γ hγR hγ
  obtain ⟨σ, hσ, hσzero, hσW, hσR, hσL, f, p, hf, hpf⟩ := hcollars c hcW
  let B := (connectedComponentComplex (boundaryComplex 3 R) c).space
  let J := r '' stdSimplexBoundary 2
  let A := σ '' (J ×ˢ Icc (0 : ℝ) 1)
  have hJB : J ⊆ B := hb
  have hJD : J ⊆ D := hDr.symm.subset.trans inter_subset_left
  have hJpoly : IsPolyhedron J := hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron
  have hA : IsPLHomeomorphOn σ (J ×ˢ Icc (0 : ℝ) 1) A :=
    hσ.restrict (hJpoly.prod isHPolytope_Icc.isPolyhedron) (prod_mono hJB Subset.rfl)
  have hAW : A ⊆ W := (image_mono (prod_mono hJB Subset.rfl)).trans hσW
  have hAmeet : A ∩ D = J := by
    apply Subset.antisymm
    · rintro y ⟨hyA, hyD⟩
      have hyB : y ∈ B := hσR.subset
        ⟨(image_mono (prod_mono hJB Subset.rfl)) hyA, hDR hyD⟩
      exact hDr.subset ⟨hyD, by
        change y ∈ (connectedComponentComplex (boundaryComplex 3 R) c).space at hyB
        rw [connectedComponentComplex_space] at hyB
        obtain ⟨z, _, rfl⟩ := hyB
        exact z.property⟩
    · intro y hy
      exact ⟨⟨(y, 0), ⟨hy, by norm_num⟩, hσzero y (hJB hy)⟩, hJD hy⟩
  obtain ⟨q, hq, hqboundary, _⟩ := hr.exists_isPLHomeomorphOn_union_collar
    (by norm_num : (0 : ℝ) < 1) hA (fun y hy => hσzero y (hJB hy)) hAmeet
  have hDint : D ⊆ K.space \ (boundaryComplex 3 K).space := by
    intro y hy
    refine ⟨hRK (hDR hy), ?_⟩
    intro hyboundary
    have hyJ : y ∈ J := hDr.subset ⟨hy, hboundary hyboundary⟩
    exact (hW (hcW (hJB hyJ))).2 hyboundary
  have hqL : q '' stdSimplexBoundary 2 ⊆ L.space := by
    rw [hqboundary]
    rintro y ⟨z, hz, rfl⟩
    exact (hσL z ⟨hJB hz.1, hz.2.symm ▸ (by norm_num)⟩).mpr hz.2
  have hinter : (D ∪ A) ∩ L.space = q '' stdSimplexBoundary 2 := by
    rw [hqboundary]
    apply Subset.antisymm
    · rintro y ⟨hy | hy, hyL⟩
      · exact (disjoint_left.mp hRL (hDR hy) hyL).elim
      · obtain ⟨z, hz, rfl⟩ := hy
        exact ⟨z, ⟨hz.1, (hσL z ⟨hJB hz.1, hz.2⟩).mp hyL⟩, rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      have hzI : z.2 ∈ Icc (0 : ℝ) 1 := hz.2.symm ▸ (by norm_num)
      exact ⟨Or.inr ⟨z, ⟨hz.1, hzI⟩, rfl⟩,
        (hσL z ⟨hJB hz.1, hzI⟩).mpr hz.2⟩
  refine ⟨D ∪ A, q, hq, union_subset hDint (hAW.trans hW), hinter, hqL, ?_⟩
  intro hnull
  let b : C(J, B) := ⟨Set.inclusion hJB, continuous_inclusion hJB⟩
  have hemem (y : J) : (f (b y) : E) ∈ q '' stdSimplexBoundary 2 := by
    rw [hqboundary, hf]
    exact ⟨(y, 1), ⟨y.property, rfl⟩, rfl⟩
  let e : C(J, q '' stdSimplexBoundary 2) :=
    ⟨fun y => ⟨f (b y), hemem y⟩,
      (continuous_subtype_val.comp (f.continuous.comp b.continuous)).subtype_mk hemem⟩
  have heq : p.comp
      ((⟨Set.inclusion hqL, continuous_inclusion hqL⟩ :
        C(q '' stdSimplexBoundary 2, L.space)).comp e) = b := by
    ext y
    exact congrArg Subtype.val (hpf (b y))
  apply hessential
  change b.Nullhomotopic
  rw [← heq]
  exact (hnull.comp_left e).comp_right p

end DifferentialGeometry.Topology.PiecewiseLinear
