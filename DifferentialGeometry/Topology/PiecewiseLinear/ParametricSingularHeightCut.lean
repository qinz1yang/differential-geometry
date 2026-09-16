import DifferentialGeometry.Topology.PiecewiseLinear.SingularHeightCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLSphere_pair_of_mem_heightSingularPoints_with_parameterized_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (A B D : Set E) (f fA fB : (Fin 3 → ℝ) → E),
      A ∪ B = K.space ∧ A ∩ B = f '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn fA (stdSimplex ℝ (Fin 3)) A ∧
      fA '' stdSimplexBoundary 2 = f '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn fB (stdSimplex ℝ (Fin 3)) B ∧
      fB '' stdSimplexBoundary 2 = f '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D ∧
      D ⊆ W ∩ {x | ℓ x = ℓ p} ∧ D ∉ 𝓝[{x | ℓ x = ℓ p}] p ∧
      IsPLSphere 2 (A ∪ D) ∧ IsPLSphere 2 (B ∪ D) ∧ (A ∪ D) ∩ (B ∪ D) = D ∧
      ((A ∪ D) ∪ (B ∪ D)) \ (D \ (f '' stdSimplexBoundary 2)) = K.space ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      (∀ r ≠ ℓ p, (levelPolygons K.space ℓ r).encard =
        (levelPolygons (A ∪ D) ℓ r).encard + (levelPolygons (B ∪ D) ℓ r).encard) ∧
      heightSingularPoints (A ∪ D) ℓ \ D =
        (heightSingularPoints K.space ℓ ∩ A) \ D ∧
      heightSingularPoints (B ∪ D) ℓ \ D =
        (heightSingularPoints K.space ℓ ∩ B) \ D ∧
      K.space ∩ D = f '' stdSimplexBoundary 2 := by
  have hman := hK.isCombinatorialManifold
  obtain ⟨D, f, hf, hJ, hSD, hDW, hpD⟩ :=
    exists_spanning_disk_of_mem_heightSingularPoints K hman hdimE ℓ hℓ hinj hp hW hWconv hKW
  obtain ⟨A, B, hunion, hinter, ⟨fA, fB, hfA, hfB, hfAJ, hfBJ⟩,
    hSA, hSB, hcap, hrecover⟩ :=
    exists_isPLSphere_pair_of_spanning_disk hK hf hSD
  have hA : IsPLBall 2 A := ⟨fA, hfA⟩
  have hB : IsPLBall 2 B := ⟨fB, hfB⟩
  have hD : IsPLBall 2 D := ⟨f, hf⟩
  have hAB : A ∩ B ⊆ D := hinter.subset.trans (hSD.symm.subset.trans inter_subset_right)
  have hpv := heightSingularPoints_subset_vertices K
    hman.isCombinatorialManifoldWithBoundary hdimE ℓ hℓ hinj hp
  refine ⟨A, B, D, f, fA, fB, hunion, hinter, hfA, hfAJ, hfB, hfBJ, hf,
    hDW, hpD, hSA, hSB, hcap, hrecover,
    encard_levelPolygons_add_of_cut_at_vertex K hman hdimE ℓ hℓ hinj hpv
      hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hunion hinter hJ, ?_, ?_, ?_, hSD⟩
  · intro r hr
    rw [← hunion]
    exact encard_levelPolygons_cap_eq hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed ℓ
      ℓ.continuous_of_finiteDimensional hAB (hDW.trans inter_subset_right) hr
  · rw [← hunion]
    exact heightSingularPoints_cap_sdiff hB.isPolyhedron.isClosed hD.isPolyhedron.isClosed
      hAB ℓ
  · rw [← hunion, union_comm A B]
    exact heightSingularPoints_cap_sdiff hA.isPolyhedron.isClosed hD.isPolyhedron.isClosed
      ((inter_comm B A).trans_le hAB) ℓ

end DifferentialGeometry.Topology.PiecewiseLinear
