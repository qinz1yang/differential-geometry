/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedSphereBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePositiveConjugation
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSubdiskOrientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLSphere.isPLCirclePositive_iff_of_disk_family
    {ι : Type*} {S : Set E} (hS : IsPLSphere 2 S)
    {D : ι → Set E} {q : ι → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDS : ∀ i, D i ⊆ S) (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    {G : E → E} (hG : IsPLHomeomorphOn G S S) (hGD : ∀ i, G '' D i = D i) (i j : ι) :
    IsPLCirclePositive (q i '' stdSimplexBoundary 2) G ↔
      IsPLCirclePositive (q j '' stdSimplexBoundary 2) G := by
  classical
  by_cases hij : i = j
  · subst i
    rfl
  let J := fun k => q k '' stdSimplexBoundary 2
  have hJD (k : ι) : J k ⊆ D k :=
    image_subset_iff.mpr fun _ hx => (hq k).bijOn.mapsTo hx.1
  have hGdisk (k : ι) : IsPLHomeomorphOn G (D k) (D k) := by
    have h := hG.restrict (IsPLBall.isPolyhedron ⟨q k, hq k⟩) (hDS k)
    rwa [hGD k] at h
  have hGJ (k : ι) : G '' J k = J k := by
    simpa only [J, image_comp] using ((hq k).trans (hGdisk k)).image_stdSimplexBoundary_congr (hq k)
  let C := S \ (D j \ J j)
  have hC : IsPLBall 2 C := by
    have h := hS.isPLBall_closure_sdiff (show IsPLBall 2 (D j) from ⟨q j, hq j⟩) (hDS j)
    rwa [hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary (hq j) (hDS j)] at h
  have hGC : G '' C = C := by
    change G '' (S \ (D j \ J j)) = S \ (D j \ J j)
    rw [hG.bijOn.injOn.image_sdiff_subset (sdiff_subset.trans (hDS j)), hG.image_eq,
      (hGdisk j).bijOn.injOn.image_sdiff_subset (hJD j), hGD j, hGJ j]
  have hGcomp : IsPLHomeomorphOn G C C := by
    have h := hG.restrict hC.isPolyhedron sdiff_subset
    rwa [hGC] at h
  obtain ⟨χ, A, hA, hχ, hχJ, hχi⟩ := hS.exists_holed_chart hq hDS hdis j
  obtain ⟨hiC, hiA, hχD, hχJi⟩ := hχi i hij
  let f := χ ∘ G ∘ Function.invFunOn χ C
  have hf : IsPLHomeomorphOn f A A := (hχ.symm.trans hGcomp).trans hχ
  have hfD : f '' (χ '' D i) = χ '' D i := by
    rw [← image_comp]
    have heq : EqOn (f ∘ χ) (χ ∘ G) (D i) := by
      intro x hx
      change χ (G (Function.invFunOn χ C (χ x))) = χ (G x)
      rw [hχ.bijOn.invOn_invFunOn.1 (hiC hx)]
    rw [heq.image_eq, image_comp, hGD i]
  have hsub := isPLCirclePositive_frontier_iff_of_subdisk hA
    ((show IsPLBall 2 (D i) from ⟨q i, hq i⟩).of_isPLHomeomorphOn hχD)
    (hiA.trans interior_subset) hf hfD
  have hJjC : J j ⊆ C := fun _ hx => ⟨hDS j (hJD j hx), fun h => h.2 hx⟩
  have hi := hχ.isPLCirclePositive_conj_iff ((hJD i).trans hiC)
    (fun _ hx => hGJ i ▸ mem_image_of_mem G hx)
  have hj := hχ.isPLCirclePositive_conj_iff hJjC
    (fun _ hx => hGJ j ▸ mem_image_of_mem G hx)
  rw [hχJi] at hi
  rw [hχJ] at hj
  exact hi.symm.trans (hsub.trans hj)

theorem IsPLSphere.exists_disk_family_map_reversing_circles
    {ι : Type*} [Finite ι] {S : Set E} (hS : IsPLSphere 2 S)
    {D : ι → Set E} {q : ι → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDS : ∀ i, D i ⊆ S) (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    ∃ G : E → E, IsPLHomeomorphOn G S S ∧ (∀ i, G '' D i = D i) ∧
      ∀ i, ¬ IsPLCirclePositive (q i '' stdSimplexBoundary 2) G := by
  classical
  by_cases hι : Nonempty ι
  · let i₀ := Classical.choice hι
    obtain ⟨G, hG, hGD, hneg⟩ :=
      hS.exists_disk_family_map_not_isPLCirclePositive hq hDS hdis i₀
    exact ⟨G, hG, hGD, fun i hi =>
      hneg ((hS.isPLCirclePositive_iff_of_disk_family hq hDS hdis hG hGD i i₀).mp hi)⟩
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨id, hS.isPolyhedron.isPLHomeomorphOn_id, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

end DifferentialGeometry.Topology.PiecewiseLinear
