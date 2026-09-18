import DifferentialGeometry.Topology.PiecewiseLinear.ConeStarCover
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleRelBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_forall_exists_isPiecewiseAffineOn_triangle_mapsTo_of_vertex_boundary
    {v : Fin 3 → E} (hv : AffineIndependent ℝ v) {L : Geometry.SimplicialComplex ℝ F}
    [Finite L.faces] {f : E → F} (hf : ContinuousOn f (convexHull ℝ (range v)))
    (hmap : MapsTo f (convexHull ℝ (range v)) L.space) :
    ∃ δ > 0, ∀ (M N : ℕ) (u σ : ℕ → ℝ),
      u 0 = 0 → u (M + 1) = 1 → (∀ j ≤ M, u j < u (j + 1)) → (∀ j ≤ M, u (j + 1) - u j < δ) →
      σ 0 = 0 → σ (N + 1) = 1 → (∀ k ≤ N, σ k < σ (k + 1)) → (∀ k ≤ N, σ (k + 1) - σ k < δ) →
      (∀ j ≤ M + 1, f (AffineMap.lineMap (v 2) (v 1) (u j)) ∈ L.vertices) →
      (∀ k ≤ N + 1, f (AffineMap.lineMap (v 0) (v 2) (σ k)) ∈ L.vertices) →
      (∀ k ≤ N + 1, f (AffineMap.lineMap (v 0) (v 1) (σ k)) ∈ L.vertices) →
      ∃ Ψ : E → F, IsPiecewiseAffineOn Ψ (convexHull ℝ (range v)) ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (AffineMap.lineMap (v 0) (v 2) t) =
            AffineMap.lineMap (f (AffineMap.lineMap (v 0) (v 2) (σ k)))
              (f (AffineMap.lineMap (v 0) (v 2) (σ (k + 1))))
              ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (AffineMap.lineMap (v 0) (v 1) t) =
            AffineMap.lineMap (f (AffineMap.lineMap (v 0) (v 1) (σ k)))
              (f (AffineMap.lineMap (v 0) (v 1) (σ (k + 1))))
              ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ j ≤ M, ∀ r ∈ Icc (u j) (u (j + 1)),
          Ψ (AffineMap.lineMap (v 2) (v 1) r) =
            AffineMap.lineMap (f (AffineMap.lineMap (v 2) (v 1) (u j)))
              (f (AffineMap.lineMap (v 2) (v 1) (u (j + 1))))
              ((r - u j) / (u (j + 1) - u j))) ∧
        (∀ x ∈ convexHull ℝ (range v), Ψ x ∈ convexHull ℝ (carrierFace L (f x))) ∧
        MapsTo Ψ (convexHull ℝ (range v)) L.space := by
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
  have hmapA : MapsTo (f ∘ triangleAffineMap v) stdCone L.space := fun z hz =>
    hmap (hbij.mapsTo hz)
  obtain ⟨δ, hδ, hmain⟩ :=
    exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_mapsTo_of_vertex_boundary hfA hmapA
  refine ⟨δ, hδ, ?_⟩
  intro M N u σ hu0 huM humono humesh hσ0 hσN hσmono hσmesh hvH hv₁ hv₂
  have hσchain := le_of_chain (fun k hk => (hσmono k hk).le)
  have hσ01 : ∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)), t ∈ Icc (0 : ℝ) 1 := by
    intro k hk t ht
    have h1 := hσchain k (by omega) 0 (Nat.zero_le _)
    have h2 := hσchain (N + 1) le_rfl (k + 1) (by omega)
    rw [hσ0] at h1
    rw [hσN] at h2
    exact ⟨le_trans h1 ht.1, le_trans ht.2 h2⟩
  obtain ⟨Ψ, hPA, hleg₁, hleg₂, hhyp, hcarrier, hmapsto⟩ :=
    hmain M N u σ hu0 huM humono humesh hσ0 hσN hσmono hσmesh
      (by
        intro j hj
        simp only [Function.comp_apply, triangleAffineMap_apply_hypotenuse]
        exact hvH j hj)
      (by
        intro k hk
        simp only [Function.comp_apply, triangleAffineMap_apply_bottom]
        exact hv₁ k hk)
      (by
        intro k hk
        simp only [Function.comp_apply, triangleAffineMap_apply_left]
        exact hv₂ k hk)
  have hinv : ∀ z ∈ stdCone, Function.invFunOn (triangleAffineMap v) stdCone
      (triangleAffineMap v z) = z :=
    fun z hz => hbij.invOn_invFunOn.1 hz
  refine ⟨Ψ ∘ Function.invFunOn (triangleAffineMap v) stdCone, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsub : convexHull ℝ (range v) ⊆
        Function.invFunOn (triangleAffineMap v) stdCone ⁻¹' stdCone :=
      fun x hx => hbij.surjOn.mapsTo_invFunOn hx
    have hcomp := hPA.comp hpl.2.2
    rwa [inter_eq_self_of_subset_left hsub] at hcomp
  · intro k hk t ht
    have hmem : ((t, 0) : ℝ × ℝ) ∈ stdCone :=
      ⟨(hσ01 k hk t ht).1, le_rfl, by simpa using (hσ01 k hk t ht).2⟩
    rw [← triangleAffineMap_apply_bottom, Function.comp_apply, hinv _ hmem]
    simpa only [Function.comp_apply, triangleAffineMap_apply_bottom] using hleg₁ k hk t ht
  · intro k hk t ht
    have hmem : ((0, t) : ℝ × ℝ) ∈ stdCone :=
      ⟨le_rfl, (hσ01 k hk t ht).1, by simpa using (hσ01 k hk t ht).2⟩
    rw [← triangleAffineMap_apply_left, Function.comp_apply, hinv _ hmem]
    simpa only [Function.comp_apply, triangleAffineMap_apply_left] using hleg₂ k hk t ht
  · intro j hj r hr
    have huchain := le_of_chain (fun i hi => (humono i hi).le)
    have h1 := huchain j (by omega) 0 (Nat.zero_le _)
    have h2 := huchain (M + 1) le_rfl (j + 1) (by omega)
    rw [hu0] at h1
    rw [huM] at h2
    have hmem : ((1 - r, r) : ℝ × ℝ) ∈ stdCone := by
      refine ⟨by linarith [hr.2, h2], by linarith [hr.1], by linarith⟩
    rw [← triangleAffineMap_apply_hypotenuse, Function.comp_apply, hinv _ hmem]
    simpa only [Function.comp_apply, triangleAffineMap_apply_hypotenuse] using hhyp j hj r hr
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := himage.symm.subset hx
    rw [Function.comp_apply, hinv _ hz]
    exact hcarrier z hz
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := himage.symm.subset hx
    rw [Function.comp_apply, hinv _ hz]
    exact hmapsto hz

end DifferentialGeometry.Topology.PiecewiseLinear
