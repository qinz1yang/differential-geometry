/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskRelBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isHPolytope_stdCone : IsHPolytope stdCone := by
  rw [← stdConeLayer_zero_one]
  exact isHPolytope_stdConeLayer le_rfl

theorem triangleAffineMap_apply_bottom (v : Fin 3 → E) (t : ℝ) :
    triangleAffineMap v (t, 0) = AffineMap.lineMap (v 0) (v 2) t := by
  rw [triangleAffineMap_apply, AffineMap.lineMap_apply_module]
  module

theorem triangleAffineMap_apply_left (v : Fin 3 → E) (t : ℝ) :
    triangleAffineMap v (0, t) = AffineMap.lineMap (v 0) (v 1) t := by
  rw [triangleAffineMap_apply, AffineMap.lineMap_apply_module]
  module

theorem triangleAffineMap_apply_hypotenuse (v : Fin 3 → E) (r : ℝ) :
    triangleAffineMap v (1 - r, r) = AffineMap.lineMap (v 2) (v 1) r := by
  rw [triangleAffineMap_apply, AffineMap.lineMap_apply_module]
  module

theorem bijOn_triangleAffineMap {v : Fin 3 → E} (hv : AffineIndependent ℝ v) :
    BijOn (triangleAffineMap v) stdCone (convexHull ℝ (range v)) := by
  have himage : triangleAffineMap v '' stdCone = convexHull ℝ (range v) :=
    triangleAffineMap_image v
  exact ⟨fun z hz => himage ▸ mem_image_of_mem _ hz,
    (triangleAffineMap_injective hv).injOn, fun x hx => himage ▸ hx⟩

variable [FiniteDimensional ℝ E]

theorem exists_pos_forall_exists_isPiecewiseAffineOn_triangle_eqOn_boundary
    {v : Fin 3 → E} (hv : AffineIndependent ℝ v) (f : E → F)
    (hf : ContinuousOn f (convexHull ℝ (range v))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (M N : ℕ) (u σ : ℕ → ℝ) (gHyp gLeg₁ gLeg₂ : ℕ → F),
      u 0 = 0 → u (M + 1) = 1 → (∀ j ≤ M, u j < u (j + 1)) → (∀ j ≤ M, u (j + 1) - u j < δ) →
      σ 0 = 0 → σ (N + 1) = 1 → (∀ k ≤ N, σ k < σ (k + 1)) → (∀ k ≤ N, σ (k + 1) - σ k < δ) →
      (∀ j ≤ M + 1, dist (gHyp j) (f (AffineMap.lineMap (v 2) (v 1) (u j))) ≤ ε) →
      (∀ k ≤ N + 1, dist (gLeg₁ k) (f (AffineMap.lineMap (v 0) (v 2) (σ k))) ≤ ε) →
      (∀ k ≤ N + 1, dist (gLeg₂ k) (f (AffineMap.lineMap (v 0) (v 1) (σ k))) ≤ ε) →
      gLeg₁ 0 = gLeg₂ 0 → gHyp 0 = gLeg₁ (N + 1) → gHyp (M + 1) = gLeg₂ (N + 1) →
      ∃ Ψ : E → F, IsPiecewiseAffineOn Ψ (convexHull ℝ (range v)) ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (AffineMap.lineMap (v 0) (v 2) t) =
            AffineMap.lineMap (gLeg₁ k) (gLeg₁ (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (AffineMap.lineMap (v 0) (v 1) t) =
            AffineMap.lineMap (gLeg₂ k) (gLeg₂ (k + 1)) ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ j ≤ M, ∀ r ∈ Icc (u j) (u (j + 1)),
          Ψ (AffineMap.lineMap (v 2) (v 1) r) =
            AffineMap.lineMap (gHyp j) (gHyp (j + 1)) ((r - u j) / (u (j + 1) - u j))) ∧
        ∀ x ∈ convexHull ℝ (range v), dist (Ψ x) (f x) ≤ 2 * ε := by
  classical
  have himage : triangleAffineMap v '' stdCone = convexHull ℝ (range v) :=
    triangleAffineMap_image v
  have hbij := bijOn_triangleAffineMap hv
  have hpl : IsPLHomeomorphOn (triangleAffineMap v) stdCone (convexHull ℝ (range v)) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_stdCone.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope (triangleAffineMap v) isHPolytope_stdCone)
      hbij
  have hfA : ContinuousOn (f ∘ triangleAffineMap v) stdCone :=
    hf.comp (triangleAffineMap v).continuous_of_finiteDimensional.continuousOn hbij.mapsTo
  obtain ⟨δ, hδ, hmain⟩ :=
    exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_eqOn_boundary
      (f ∘ triangleAffineMap v) hfA hε
  refine ⟨δ, hδ, ?_⟩
  intro M N u σ gHyp gLeg₁ gLeg₂ hu0 huM humono humesh hσ0 hσN hσmono hσmesh hclH hcl₁ hcl₂
    hc₀ hc₁ hc₂
  have hσchain := le_of_chain (fun k hk => (hσmono k hk).le)
  have hσ01 : ∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)), t ∈ Icc (0 : ℝ) 1 := by
    intro k hk t ht
    have h1 := hσchain k (by omega) 0 (Nat.zero_le _)
    have h2 := hσchain (N + 1) le_rfl (k + 1) (by omega)
    rw [hσ0] at h1
    rw [hσN] at h2
    exact ⟨le_trans h1 ht.1, le_trans ht.2 h2⟩
  obtain ⟨Ψ, hPA, hleg₁, hleg₂, hhyp, hdist⟩ :=
    hmain M N u σ gHyp gLeg₁ gLeg₂ hu0 huM humono humesh hσ0 hσN hσmono hσmesh
      (by
        intro j hj
        simp only [Function.comp_apply, triangleAffineMap_apply_hypotenuse]
        exact hclH j hj)
      (by
        intro k hk
        simp only [Function.comp_apply, triangleAffineMap_apply_bottom]
        exact hcl₁ k hk)
      (by
        intro k hk
        simp only [Function.comp_apply, triangleAffineMap_apply_left]
        exact hcl₂ k hk)
      hc₀ hc₁ hc₂
  have hinv : ∀ z ∈ stdCone, Function.invFunOn (triangleAffineMap v) stdCone
      (triangleAffineMap v z) = z :=
    fun z hz => hbij.invOn_invFunOn.1 hz
  refine ⟨Ψ ∘ Function.invFunOn (triangleAffineMap v) stdCone, ?_, ?_, ?_, ?_, ?_⟩
  · have hsub : convexHull ℝ (range v) ⊆
        Function.invFunOn (triangleAffineMap v) stdCone ⁻¹' stdCone :=
      fun x hx => hbij.surjOn.mapsTo_invFunOn hx
    have hcomp := hPA.comp hpl.2.2
    rwa [inter_eq_self_of_subset_left hsub] at hcomp
  · intro k hk t ht
    have hmem : ((t, 0) : ℝ × ℝ) ∈ stdCone :=
      ⟨(hσ01 k hk t ht).1, le_rfl, by simpa using (hσ01 k hk t ht).2⟩
    rw [← triangleAffineMap_apply_bottom, Function.comp_apply, hinv _ hmem]
    exact hleg₁ k hk t ht
  · intro k hk t ht
    have hmem : ((0, t) : ℝ × ℝ) ∈ stdCone :=
      ⟨le_rfl, (hσ01 k hk t ht).1, by simpa using (hσ01 k hk t ht).2⟩
    rw [← triangleAffineMap_apply_left, Function.comp_apply, hinv _ hmem]
    exact hleg₂ k hk t ht
  · intro j hj r hr
    have huchain := le_of_chain (fun i hi => (humono i hi).le)
    have h1 := huchain j (by omega) 0 (Nat.zero_le _)
    have h2 := huchain (M + 1) le_rfl (j + 1) (by omega)
    rw [hu0] at h1
    rw [huM] at h2
    have hmem : ((1 - r, r) : ℝ × ℝ) ∈ stdCone := by
      refine ⟨by linarith [hr.2, h2], by linarith [hr.1], by linarith⟩
    rw [← triangleAffineMap_apply_hypotenuse, Function.comp_apply, hinv _ hmem]
    exact hhyp j hj r hr
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := himage.symm.subset hx
    rw [Function.comp_apply, hinv _ hz]
    exact hdist z hz

end DifferentialGeometry.Topology.PiecewiseLinear
