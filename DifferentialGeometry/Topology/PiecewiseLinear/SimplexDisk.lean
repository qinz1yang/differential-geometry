/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCornerChart
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isPLHomeomorphOn_straighten_to_face_in_simplex_vertex_star [FiniteDimensional ℝ E]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 4) (hspan : affineSpan ℝ (T : Set E) = ⊤) {a : E} (ha : a ∈ T)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    (hDstar : K.space ⊆ openStar (simplexBoundary T hT) a)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = 3)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      h '' K.space = convexHull ℝ (s : Set E) ∧
      EqOn h id (convexHull ℝ ((T.erase a : Finset E) : Set E)) ∧ EqOn h id Uᶜ := by
  classical
  let D := K.space
  let L := starComplex (simplexBoundary T hT) a
  have hDL : D ⊆ L.space := by
    intro x hx
    have h := hDstar hx
    rw [openStar_simplexBoundary_eq_sdiff_boundary T hT (by omega) ha] at h
    exact h.1
  obtain ⟨S, f, hS, -, hf, hAff, hB, hopen⟩ :=
    exists_isPLHomeomorphOn_simplex_vertex_star_euclidean T hT (n := 1) hcard ha
  let Q := convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))
  have hQ : IsPolyhedron Q := (isHPolytope_convexHull_of_affineIndependent S hS).isPolyhedron
  have hKD : K.space = D := rfl
  have hKL : K.space ⊆ L.space := hDL
  have hKball : IsPLBall 2 K.space := hK
  have hKAff : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
      EqOn f A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := exists_simplex_vertex_star_face_convexHull_subset T hT a
      (K.nonempty_of_mem_faces hs) ((K.convexHull_subset_space hs).trans hDstar)
    obtain ⟨A, hA⟩ := hAff t ht
    exact ⟨A, hA.mono hst⟩
  obtain ⟨M, hMfin, hMspace, hMfaces, hfM⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces K hKAff (hf.bijOn.injOn.mono hKL)
  have : Finite M.faces := hMfin.to_subtype
  have hMball : IsPLBall 2 M.space := hKball.of_isPLHomeomorphOn hfM
  have hinjs : InjOn f (s : Set E) :=
    hf.bijOn.injOn.mono ((K.subset_space hs).trans hKL)
  have hsf : s.image f ∈ M.faces := (hMfaces _).mpr ⟨s, hs, rfl⟩
  have hsfcard : (s.image f).card = 3 := by rw [Finset.card_image_of_injOn hinjs, hscard]
  have hsD : convexHull ℝ (s : Set E) ⊆ D := (K.convexHull_subset_space hs).trans_eq hKD
  have hMQ : M.space ⊆ interior Q := by
    rw [hMspace, hKD, ← hopen]
    exact image_mono hDstar
  obtain ⟨g, hg, hgM, hgfix⟩ :=
    exists_isPLHomeomorphOn_straighten_to_face M hMball hsf hsfcard isOpen_interior hMQ
  have hgfixQ : EqOn g id Qᶜ := hgfix.mono (compl_subset_compl.mpr interior_subset)
  have hgQbij : BijOn g Q Q := by
    have h := ((bijOn_id Qᶜ).congr hgfixQ.symm).compl g.bijective
    simpa only [compl_compl] using h
  have hgQ : IsPLHomeomorphOn g Q Q := by
    have h := hg.restrict hQ (subset_univ Q)
    rwa [hgQbij.image_eq] at h
  have hgB : ∀ x ∈ (simplexBoundary (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T))).space, g (f x) = f x := by
    intro x hx
    have hxB : f x ∈ frontier Q := hB ▸ (show f x ∈ f '' _ from ⟨x, hx, rfl⟩)
    exact hgfix hxB.2
  obtain ⟨h, hh, hC, hhf, hhF, hhU, -⟩ :=
    exists_isPLHomeomorphOn_extension_simplex_vertex_star_of_chart T hT (by omega) hspan ha
      hf hgQ hgB hU hTU
  have hsfImage : f '' convexHull ℝ (s : Set E) =
      convexHull ℝ ((s.image f : Finset (EuclideanSpace ℝ (Fin 2))) : Set _) := by
    obtain ⟨A, hA⟩ := hKAff s hs
    have hv : f '' (s : Set E) = A '' (s : Set E) :=
      (hA.mono (subset_convexHull ℝ _)).image_eq
    rw [hA.image_eq, A.image_convexHull, Finset.coe_image, hv]
  have hgD : g '' (f '' D) = convexHull ℝ ((s.image f : Finset _) : Set _) := by
    rwa [hMspace, hKD] at hgM
  have hinv : EqOn (Function.invFunOn f L.space ∘ f) id (convexHull ℝ (s : Set E)) :=
    fun x hx => hf.bijOn.invOn_invFunOn.1 (hDL (hsD hx))
  refine ⟨h, hh, hC, ?_, hhF, hhU⟩
  calc
    h '' D = Function.invFunOn f L.space '' (g '' (f '' D)) := by
      rw [(hhf.mono hDL).image_eq]
      simp only [image_image, Function.comp_def, L]
    _ = Function.invFunOn f L.space '' convexHull ℝ ((s.image f : Finset _) : Set _) := by rw [hgD]
    _ = convexHull ℝ (s : Set E) := by
      rw [← hsfImage, image_image]
      change (Function.invFunOn f L.space ∘ f) '' convexHull ℝ (s : Set E) = _
      rw [hinv.image_eq, image_id]

theorem exists_isPLHomeomorphOn_straighten_disk_in_simplex_vertex_star [FiniteDimensional ℝ E]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = 4) (hspan : affineSpan ℝ (T : Set E) = ⊤) {a : E} (ha : a ∈ T)
    {D : Set E} (hD : IsPLBall 2 D) (hDstar : D ⊆ openStar (simplexBoundary T hT) a)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ (s : Finset E) (h : E ≃ₜ E), AffineIndependent ℝ ((↑) : s → E) ∧ s.card = 3 ∧
      convexHull ℝ (s : Set E) ⊆ D ∧ IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      h '' D = convexHull ℝ (s : Set E) ∧
      EqOn h id (convexHull ℝ ((T.erase a : Finset E) : Set E)) ∧ EqOn h id Uᶜ := by
  obtain ⟨K, hKfin, hKD⟩ := hD.isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKD.symm ▸ hD
  obtain ⟨x, hx⟩ := hK.nonempty
  obtain ⟨t, ht, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨s, hs, -, hscard⟩ := exists_face_superset_card_eq_of_isPLBall K hK ht
  obtain ⟨h, hh, hC, hKD', hF, hU'⟩ :=
    exists_isPLHomeomorphOn_straighten_to_face_in_simplex_vertex_star T hT hcard hspan ha
      K hK (hKD.trans_le hDstar) hs hscard hU hTU
  refine ⟨s, h, K.indep hs, hscard, (K.convexHull_subset_space hs).trans_eq hKD,
    hh, hC, ?_, hF, hU'⟩
  rwa [hKD] at hKD'

end DifferentialGeometry.Topology.PiecewiseLinear
