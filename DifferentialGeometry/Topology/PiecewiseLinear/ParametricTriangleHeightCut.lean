import DifferentialGeometry.Topology.PiecewiseLinear.ParametricSingularHeightCut
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleConvexification
import DifferentialGeometry.Topology.PiecewiseLinear.HeightLocalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_parameterized_triangle_cut_of_singular_height
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (A B D : Set E) (g fA fB : (Fin 3 → ℝ) → E) (H : E ≃ₜ E)
      (m : E →ₗ[ℝ] ℝ) (e : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] E)
      (T : Finset (EuclideanSpace ℝ (Fin 2))),
      A ∪ B = K.space ∧ A ∩ B = g '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn fA (stdSimplex ℝ (Fin 3)) A ∧
      fA '' stdSimplexBoundary 2 = g '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn fB (stdSimplex ℝ (Fin 3)) B ∧
      fB '' stdSimplexBoundary 2 = g '' stdSimplexBoundary 2 ∧
      K.space ∩ D = g '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D ∧
      D ⊆ W ∩ {x | ℓ x = ℓ p} ∧ D ∉ 𝓝[{x | ℓ x = ℓ p}] p ∧
      IsPLSphere 2 (A ∪ D) ∧ IsPLSphere 2 (B ∪ D) ∧ (A ∪ D) ∩ (B ∪ D) = D ∧
      ((A ∪ D) ∪ (B ∪ D)) \ (D \ (g '' stdSimplexBoundary 2)) = K.space ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Wᶜ ∧ EqOn H id (K.vertices \ {p}) ∧
      (∀ x, ℓ (H x) = ℓ x) ∧ Convex ℝ (H '' D) ∧
      T.card = 3 ∧ AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)) ∧
      Function.Injective e ∧ H '' D = e '' convexHull ℝ (T : Set _) ∧
      m ≠ 0 ∧ (∀ x ∈ H '' D \ {H p}, m (H p) < m x) ∧
      (∀ S : Set E, heightIndex (H '' S) ℓ = heightIndex S ℓ) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hpv := heightSingularPoints_subset_vertices K
    hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
    hdimE ℓ.toLinearMap hlinear hinj hp
  obtain ⟨A, B, D, g, fA, fB, hunion, hinter, hfA, hfAJ, hfB, hfBJ, hg,
    hDW, hpD, hAD, hBD, hcap, hrecover, hcount, -, -, -, hSD⟩ :=
    exists_isPLSphere_pair_of_mem_heightSingularPoints_with_parameterized_boundary
      K hK hdimE ℓ.toLinearMap hlinear hinj hp hW hWconv hKW
  have hA : IsPLBall 2 A := ⟨fA, hfA⟩
  have hB : IsPLBall 2 B := ⟨fB, hfB⟩
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  have hV : (K.vertices \ {p}).Finite :=
    (Set.Finite.preimage Finset.singleton_injective.injOn
      (Set.toFinite K.faces)).subset sdiff_subset
  have havoid : ℓ p ∉ ℓ '' (K.vertices \ {p}) := by
    rintro ⟨q, hq, heq⟩
    exact hq.2 (hinj hq.1 hpv heq)
  obtain ⟨U, C, hU, hUconv, hDU, hUW, hUC, -, hsep⟩ :=
    exists_convex_open_neighborhood_disjoint_fibers hD.isPolyhedron.isCompact ℓ
      (hDW.trans inter_subset_right) hV havoid hW hWconv
      (hDW.trans inter_subset_left)
  obtain ⟨H, m, e, T, hH, hfixU, hheight, hTcard, hT, heinj, htriangle,
    hm, hmsep, hindex⟩ :=
    exists_isPLHomeomorphOn_triangle_image_strict_separation_of_subset_fiber
      hdimE ℓ.toLinearMap hlinear hD (hDW.trans inter_subset_right) rfl hpD
      hUconv hU hDU
  have hconvex : Convex ℝ (H '' D) := by
    rw [htriangle]
    exact (convex_convexHull ℝ (T : Set _)).affine_image e
  have hfixC : EqOn H id Cᶜ := hfixU.mono (compl_subset_compl.mpr hUC)
  have hfixV : EqOn H id (K.vertices \ {p}) := by
    intro q hq
    exact hfixC (fun hqC => Set.disjoint_left.mp (hsep q hq) hqC rfl)
  exact ⟨A, B, D, g, fA, fB, H, m, e, T, hunion, hinter, hfA, hfAJ, hfB,
    hfBJ, hSD, hg, hDW, hpD, hAD, hBD, hcap, hrecover, hcount, hH,
    hfixU.mono (compl_subset_compl.mpr hUW), hfixV, hheight, hconvex,
    hTcard, hT, heinj, htriangle, hm, hmsep, hindex⟩

end DifferentialGeometry.Topology.PiecewiseLinear
