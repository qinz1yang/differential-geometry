/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSides
import DifferentialGeometry.Topology.PiecewiseLinear.ParametricTriangleHeightCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_parameterized_triangle_cut_with_opposite_height_sides
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (A B D C : Set E) (g fA fB : (Fin 3 → ℝ) → E) (H : E ≃ₜ E)
      (m : E →ₗ[ℝ] ℝ) (e : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] E)
      (T : Finset (EuclideanSpace ℝ (Fin 2))),
      A ∪ B = K.space ∧ A ∩ B = g '' stdSimplexBoundary 2 ∧
      (g '' stdSimplexBoundary 2) ∈ levelPolygons K.space ℓ (ℓ p) ∧
      IsPLHomeomorphOn fA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
      fA '' stdSimplexBoundary 2 = g '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn fB (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B ∧
      fB '' stdSimplexBoundary 2 = g '' stdSimplexBoundary 2 ∧
      K.space ∩ D = g '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ W ∩ {x | ℓ x = ℓ p} ∧ D ∉ 𝓝[{x | ℓ x = ℓ p}] p ∧
      IsPLSphere 2 (A ∪ D) ∧ IsPLSphere 2 (B ∪ D) ∧ (A ∪ D) ∩ (B ∪ D) = D ∧
      ((A ∪ D) ∪ (B ∪ D)) \ (D \ (g '' stdSimplexBoundary 2)) = K.space ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      IsCompact C ∧ D ⊆ C ∧ IsPLHomeomorphOn H univ univ ∧ EqOn H id Cᶜ ∧
      EqOn H id Wᶜ ∧ EqOn H id (K.vertices \ {p}) ∧
      (∀ x, ℓ (H x) = ℓ x) ∧ Convex ℝ (H '' D) ∧
      T.card = 3 ∧ AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)) ∧
      Function.Injective e ∧ H '' D = e '' convexHull ℝ (T : Set _) ∧
      m ≠ 0 ∧ (∀ q ∈ K.vertices \ {p}, Disjoint C {x | ℓ x = ℓ q}) ∧
      (∀ x ∈ H '' D \ {H p}, m (H p) < m x) ∧
      ((∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          (x ∈ A ↔ x ∈ K.space ∧ ℓ p ≤ ℓ x) ∧
          (x ∈ B ↔ x ∈ K.space ∧ ℓ x ≤ ℓ p)) ∨
        (∀ q ∈ g '' stdSimplexBoundary 2 \ {p}, ∀ᶠ x in 𝓝 q,
          (x ∈ A ↔ x ∈ K.space ∧ ℓ x ≤ ℓ p) ∧
          (x ∈ B ↔ x ∈ K.space ∧ ℓ p ≤ ℓ x))) ∧
      ∀ S : Set E, heightIndex (H '' S) ℓ = heightIndex S ℓ := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hman := hK.isCombinatorialManifold
  have hpv := heightSingularPoints_subset_vertices K
    hman.isCombinatorialManifoldWithBoundary hdimE ℓ.toLinearMap hlinear hinj hp
  obtain ⟨D, g, hg, hJ, hSD, hDW, hpD⟩ :=
    exists_spanning_disk_of_mem_heightSingularPoints K hman hdimE ℓ.toLinearMap
      hlinear hinj hp hW hWconv hKW
  obtain ⟨A, B, hunion, hinter, ⟨fA, fB, hfA, hfB, hfAJ, hfBJ⟩,
      hAD, hBD, hcap, hrecover⟩ :=
    exists_isPLSphere_pair_of_spanning_disk hK hg hSD
  have hA : IsPLBall 2 A := ⟨fA, hfA⟩
  have hB : IsPLBall 2 B := ⟨fB, hfB⟩
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  have hcount := encard_levelPolygons_add_of_cut_at_vertex K hman hdimE ℓ.toLinearMap
    hlinear hinj hpv hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hunion hinter hJ
  have hsides := eventually_mem_opposite_halfSpaces_along_levelPolygon_disk_partition
    K hman hdimE ℓ hℓ hinj hpv hJ hfA hfB hunion hinter hfAJ hfBJ
  have hV : (K.vertices \ {p}).Finite :=
    (Set.Finite.preimage Finset.singleton_injective.injOn
      (Set.toFinite K.faces)).subset sdiff_subset
  have havoid : ℓ p ∉ ℓ '' (K.vertices \ {p}) := by
    rintro ⟨q, hq, heq⟩
    exact hq.2 (hinj hq.1 hpv heq)
  obtain ⟨U, C, hU, hUconv, hDU, hUW, hUC, hC, hsep⟩ :=
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
  exact ⟨A, B, D, C, g, fA, fB, H, m, e, T, hunion, hinter, hJ, hfA, hfAJ, hfB,
    hfBJ, hSD, hg, hDW, hpD, hAD, hBD, hcap, hrecover, hcount, hC,
    hDU.trans hUC, hH, hfixC, hfixU.mono (compl_subset_compl.mpr hUW), hfixV,
    hheight, hconvex, hTcard, hT, heinj, htriangle, hm, hsep, hmsep, hsides, hindex⟩

end DifferentialGeometry.Topology.PiecewiseLinear
