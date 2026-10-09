/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightPerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCapPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_small_triangle_cap_pair_with_singular_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdimE : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A B D : Set E) (H : E ≃ₜ E) (R₁ R₂ : Geometry.SimplicialComplex ℝ E)
      (f : E →L[ℝ] ℝ),
      A ∪ B = K.space ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      R₁.faces.Finite ∧ R₁.space = H '' (A ∪ D) ∧
      IsPLSphere 2 R₁.space ∧
      R₂.faces.Finite ∧ R₂.space = H '' (B ∪ D) ∧
      IsPLSphere 2 R₂.space ∧
      dist f ℓ < ε ∧ f ≠ 0 ∧ InjOn f R₁.vertices ∧ InjOn f R₂.vertices ∧
      (∀ x ∈ K.vertices, ∀ y ∈ K.vertices, ℓ x < ℓ y → f x < f y) ∧
      (heightSingularPoints R₁.space f \ {H p} ⊆
          heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R₁.space f ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ A) ∧
          (levelPolygons R₁.space f (f q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard) ∧
      (heightSingularPoints R₂.space f \ {H p} ⊆
          heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R₂.space f ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ B) ∧
          (levelPolygons R₂.space f (f q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard) := by
  classical
  obtain ⟨A, B, D, H, m, U, R₁, R₂, hunion, hcount, hHD, hlevel, hH, -,
      -, hmsep, hR₁fin, hR₁space, hR₁, hR₂fin, hR₂space, hR₂, hevent⟩ :=
    exists_triangle_cap_pair_with_singular_comparison hdimE K hK ℓ hℓ hinj hp
      hW hWconv hKW
  have hR₁vertices : R₁.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hR₁fin
  have hR₂vertices : R₂.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hR₂fin
  have hgeneral : (R₁.vertices ∪ R₂.vertices ∪ (U : Set E)).Finite :=
    (hR₁vertices.union hR₂vertices).union U.finite_toSet
  have hKvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  have hclose : ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, dist f ℓ < ε :=
    Metric.ball_mem_nhds ℓ hε
  obtain ⟨δ, hδ, hδgood⟩ := Metric.mem_nhds_iff.mp (hevent.and hclose)
  obtain ⟨f, hfδ, hfne, hfinj, horder, hcap⟩ :=
    exists_continuousLinearMap_injOn_preserving_strict_order_and_halfSpace_of_isPolyhedron
      hgeneral hKvertices ℓ (LinearMap.toContinuousLinearMap m) hℓ hHD.isPolyhedron
      (H p) hlevel hmsep hδ
  obtain ⟨hcomparison, hfε⟩ := hδgood hfδ
  obtain ⟨hcomparison₁, hcomparison₂⟩ := hcomparison hfne hfinj hcap
  have hfinj₁ : InjOn f R₁.vertices :=
    hfinj.mono (subset_union_left.trans subset_union_left)
  have hfinj₂ : InjOn f R₂.vertices := by
    apply hfinj.mono
    intro x hx
    exact Or.inl (Or.inr hx)
  exact ⟨A, B, D, H, R₁, R₂, f, hunion, hcount, hR₁fin, hR₁space, hR₁,
    hR₂fin, hR₂space, hR₂, hfε, hfne, hfinj₁, hfinj₂, horder,
    hcomparison₁, hcomparison₂⟩

end DifferentialGeometry.Topology.PiecewiseLinear
