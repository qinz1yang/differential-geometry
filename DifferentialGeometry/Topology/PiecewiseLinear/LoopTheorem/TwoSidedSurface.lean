import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarComplementCollars
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarBoundaryLoop
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Orientable

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_compressing_disk_of_twoSided_surface
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : Finite K.faces)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKo : IsOrientable 3 K)
    (L : Geometry.SimplicialComplex ℝ E) (hLfin : Finite L.faces)
    (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (htwo : IsTwoSided (((↑) : K.space → E) ⁻¹' L.space))
    (x : L.space) (g : FundamentalGroup L.space x) (hg : g ≠ 1)
    (hgin : FundamentalGroup.map
      (⟨Set.inclusion (hLK.trans sdiff_subset), continuous_inclusion _⟩ : C(L.space, K.space)) x g = 1) :
    ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ K.space \ (boundaryComplex 3 K).space ∧
      Δ ∩ L.space = r '' stdSimplexBoundary 2 ∧
      ∃ hb : r '' stdSimplexBoundary 2 ⊆ L.space,
        ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ : C(r '' stdSimplexBoundary 2, L.space)).Nullhomotopic := by
  classical
  let _ : Finite K.faces := hKfin
  let _ : Finite L.faces := hLfin
  obtain ⟨W, ρ, R, hRfin, hρ, hρzero, hW, hWnhds, hR, hRspace, hRK, hRL,
      hboundary, _, hcollars⟩ :=
    exists_bicollar_complement_with_boundary_collars K L hK hL hLK htwo
  let _ : Finite R.faces := hRfin
  have hRo : IsOrientable 3 R := hKo.of_space_subset K R hRK hK hR
  obtain ⟨c, hcW, -, γ, hγR, hγ⟩ :=
    exists_nontrivial_boundary_loop_of_bicollar_complement K L R hK hL hLK hR
      W ρ hρ hρzero hW hWnhds hRspace x g hg hgin
  obtain ⟨D, r, hr, hDR, hDr, hb, hessential⟩ :=
    loop_theorem R hRfin hR hRo c γ hγR hγ
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
