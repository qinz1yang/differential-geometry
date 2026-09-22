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

/-!
# The orientable extended loop theorem from the boundary loop theorem

The assembly proves `Moise264Orientable` from `Moise252` and two open leaves. It inherits
orientability for the cut manifold using `IsOrientable.of_space_subset`, applies the boundary
loop theorem, and adds a half collar using `DiskBoundaryCollar`. The original unrestricted
`Moise264` remains open; intrinsic two-sidedness and orientability are explicit here. The
already proved Euclidean local essential-disk theorem is not replaced by this general chain.

`exists_bicollar_complement_with_boundary_collars`: a finite cut manifold and half collars
back to the original surface, including component retractions; topology lane, UNREVIEWED.
`exists_nontrivial_boundary_loop_of_bicollar_complement`: a nontrivial kernel loop transfers
to a collar-end boundary component of the same cut manifold; topology lane, UNREVIEWED.

The first leaf contains no loop or disk. The second contains no embedded disk. Its remaining
geometric argument is the innermost-circle procedure of Moise Section 26.4, including the
nonseparating case. A component retraction in the first leaf is the inverse collar-end map
on one connected surface component, extended constantly across the other clopen components.
It does not assert essentialness of any loop or boundary circle.

Common fixture, UNTESTED in Lean: a triangulated three-ball containing a standard unknotted
polyhedral torus in its interior, with a bicollar of that torus and a meridian as kernel loop.
The same collar and complementary manifold serve both leaves. No fixture certification or
proof of either leaf is claimed. Empty surfaces have no basepoint for the kernel premise;
disconnected surfaces and nonseparating two-sided surfaces are retained in the statements.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_bicollar_complement_with_boundary_collars
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (htwo : IsTwoSided (((↑) : K.space → E) ⁻¹' L.space)) :
    ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
      ∃ _ : Finite R.faces,
        IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W ∧
        (∀ y ∈ L.space, ρ (y, 0) = y) ∧
        W ⊆ K.space \ (boundaryComplex 3 K).space ∧
        W ∈ 𝓝ˢ[K.space] L.space ∧
        IsCombinatorialManifoldWithBoundary 3 R ∧
        R.space = closure (K.space \ W) ∧
        R.space ⊆ K.space ∧
        Disjoint R.space L.space ∧
        (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 R).space ∧
        (R.space ∩ W = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ))) ∧
        ∀ c : ConnectedComponents (boundaryComplex 3 R).space,
          let B := (connectedComponentComplex (boundaryComplex 3 R) c).space
          B ⊆ W →
          ∃ σ : E × ℝ → E,
            IsPLHomeomorphOn σ (B ×ˢ Icc (0 : ℝ) 1)
              (σ '' (B ×ˢ Icc (0 : ℝ) 1)) ∧
            (∀ y ∈ B, σ (y, 0) = y) ∧
            σ '' (B ×ˢ Icc (0 : ℝ) 1) ⊆ W ∧
            (σ '' (B ×ˢ Icc (0 : ℝ) 1)) ∩ R.space = B ∧
            (∀ z ∈ B ×ˢ Icc (0 : ℝ) 1, σ z ∈ L.space ↔ z.2 = 1) ∧
            ∃ (f : C(B, L.space)) (p : C(L.space, B)),
              (∀ y : B, (f y : E) = σ (y, 1)) ∧ Function.LeftInverse p f := by
  sorry

open Classical in
theorem exists_nontrivial_boundary_loop_of_bicollar_complement
    (K L R : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (W : Set E) (ρ : E × ℝ → E)
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hρzero : ∀ y ∈ L.space, ρ (y, 0) = y)
    (hW : W ⊆ K.space \ (boundaryComplex 3 K).space)
    (hWnhds : W ∈ 𝓝ˢ[K.space] L.space)
    (hRspace : R.space = closure (K.space \ W))
    (x : L.space) (g : FundamentalGroup L.space x) (hg : g ≠ 1)
    (hgin : FundamentalGroup.map
      (⟨Set.inclusion (hLK.trans sdiff_subset), continuous_inclusion _⟩ :
        C(L.space, K.space)) x g = 1) :
    ∃ c : ConnectedComponents (boundaryComplex 3 R).space,
      (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ W ∧
      ∃ hsub : (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ R.space,
      ∃ γ : freeLoop (connectedComponentComplex (boundaryComplex 3 R) c).space,
        IsNullHomotopic ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C((connectedComponentComplex (boundaryComplex 3 R) c).space, R.space)).comp γ) ∧
        ¬ IsNullHomotopic γ := by
  sorry

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
