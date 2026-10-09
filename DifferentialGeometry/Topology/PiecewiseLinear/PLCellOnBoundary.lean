/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssemblyFixture
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.dim_eq {n n' : ℕ} {P : Set E} (hP : IsPLBall n P) (hP' : IsPLBall n' P) :
    n = n' := by
  classical
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  have hfin : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall n K.space := hKP.symm ▸ hP
  have hK' : IsPLBall n' K.space := hKP.symm ▸ hP'
  obtain ⟨x, hx⟩ := hK.nonempty
  obtain ⟨s, hs, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨t, ht, -, hcard⟩ := exists_face_superset_card_eq_of_isPLBall K hK hs
  obtain ⟨t', ht', -, hcard'⟩ := exists_face_superset_card_eq_of_isPLBall K hK' hs
  have h1 := card_le_of_isPLBall K hK' ht
  have h2 := card_le_of_isPLBall K hK ht'
  omega

end Model

section Transition

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem IsPLHomeomorphInto.comp_of_image_eq {n : ℕ} {N₁ N₂ N₃ : Type*} [TopologicalSpace N₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₁] [TopologicalSpace N₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₂] [TopologicalSpace N₃]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N₃] {u : N₁ → N₂} {K : Set N₁} {G : N₂ → N₃}
    (hu : IsPLHomeomorphInto n u K) (hG : IsPLHomeomorphInto n G (u '' K)) :
    IsPLHomeomorphInto n (G ∘ u) K := by
  refine ⟨IsPLOn.comp_of_mapsTo hG.isPLOn hu.isPLOn (mapsTo_image u K),
    fun x hx y hy hxy => hu.injOn hx hy (hG.injOn ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxy), ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have hne₁ : Nonempty N₁ := ⟨x⟩
  have hne₂ : Nonempty N₂ := ⟨u x⟩
  have hset : (G ∘ u) '' K = G '' (u '' K) := image_comp G u K
  have hcomp : IsPLOn n n (Function.invFunOn u K ∘ Function.invFunOn G (u '' K))
      (G '' (u '' K)) :=
    IsPLOn.comp_of_mapsTo (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn)
      (hG.isPLOn_inverse hG.injOn.leftInvOn_invFunOn)
      hG.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  refine ⟨Function.invFunOn u K ∘ Function.invFunOn G (u '' K), ?_, fun y hy => ?_⟩
  · rw [hset]
    exact hcomp (G (u x)) ⟨u x, ⟨x, hx, rfl⟩, rfl⟩
  · simp only [Function.comp_apply, hG.injOn.leftInvOn_invFunOn ⟨y, hy, rfl⟩,
      hu.injOn.leftInvOn_invFunOn hy]

theorem IsPLHomeomorphInto.isPLHomeomorphOn_invFunOn_comp
    {P₁ P₂ : Set (EuclideanSpace ℝ (Fin 3))} {u₁ u₂ : EuclideanSpace ℝ (Fin 3) → M₁}
    (h₁ : IsPLHomeomorphInto 3 u₁ P₁) (hP₁ : IsPolyhedron P₁)
    (h₂ : IsPLHomeomorphInto 3 u₂ P₂) (hsub : u₁ '' P₁ ⊆ u₂ '' P₂) :
    IsPLHomeomorphOn (Function.invFunOn u₂ P₂ ∘ u₁) P₁
      ((Function.invFunOn u₂ P₂ ∘ u₁) '' P₁) := by
  have hmaps : MapsTo u₁ P₁ (u₂ '' P₂) := fun x hx => hsub ⟨x, hx, rfl⟩
  have hpl : IsPiecewiseAffineOn (Function.invFunOn u₂ P₂ ∘ u₁) P₁ :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (IsPLOn.comp_of_mapsTo (h₂.isPLOn_inverse h₂.injOn.leftInvOn_invFunOn) h₁.isPLOn hmaps)
  have hinj : InjOn (Function.invFunOn u₂ P₂ ∘ u₁) P₁ := by
    intro x hx y hy hxy
    simp only [Function.comp_apply] at hxy
    refine h₁.injOn hx hy ?_
    have e1 : u₂ (Function.invFunOn u₂ P₂ (u₁ x)) = u₁ x :=
      h₂.injOn.bijOn_image.invOn_invFunOn.2 (hmaps hx)
    have e2 : u₂ (Function.invFunOn u₂ P₂ (u₁ y)) = u₁ y :=
      h₂.injOn.bijOn_image.invOn_invFunOn.2 (hmaps hy)
    rw [← e1, ← e2, hxy]
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP₁ hpl hinj.bijOn_image

theorem IsPLHomeomorphInto.isPLHomeomorphOn_transition
    {P₁ P₂ : Set (EuclideanSpace ℝ (Fin 3))} {u₁ u₂ : EuclideanSpace ℝ (Fin 3) → M₁}
    (h₁ : IsPLHomeomorphInto 3 u₁ P₁) (hP₁ : IsPolyhedron P₁)
    (h₂ : IsPLHomeomorphInto 3 u₂ P₂) (himg : u₁ '' P₁ = u₂ '' P₂) :
    IsPLHomeomorphOn (Function.invFunOn u₂ P₂ ∘ u₁) P₁ P₂ := by
  have h := h₁.isPLHomeomorphOn_invFunOn_comp hP₁ h₂ himg.subset
  have hbij : BijOn (Function.invFunOn u₂ P₂) (u₂ '' P₂) P₂ :=
    h₂.injOn.bijOn_image.invOn_invFunOn.symm.bijOn
      h₂.injOn.bijOn_image.surjOn.mapsTo_invFunOn h₂.injOn.bijOn_image.mapsTo
  rwa [image_comp, himg, hbij.image_eq] at h

end Transition

section InvarianceOfDomain

variable {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]

theorem IsPLHomeomorphInto.image_interior {P : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → M₁} (hu : IsPLHomeomorphInto 3 u P) :
    u '' interior P = interior (u '' P) := by
  have hbij : BijOn u P (u '' P) := hu.injOn.bijOn_image
  have hug : ∀ y ∈ u '' P, u (Function.invFunOn u P y) = y :=
    fun y hy => hbij.invOn_invFunOn.2 hy
  have hgmaps : MapsTo (Function.invFunOn u P) (u '' P) P := hbij.surjOn.mapsTo_invFunOn
  have hgcont : ContinuousOn (Function.invFunOn u P) (u '' P) := fun y hy =>
    (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn y hy).continuousWithinAt
  have hginj : InjOn (Function.invFunOn u P) (u '' P) := by
    intro y hy z hz hyz
    rw [← hug y hy, ← hug z hz, hyz]
  refine Subset.antisymm (interior_maximal (image_mono interior_subset) ?_) ?_
  · exact isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
      (hu.continuousOn.mono interior_subset) (hu.injOn.mono interior_subset)
  · have hopen : IsOpen (Function.invFunOn u P '' interior (u '' P)) :=
      isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
        (hgcont.mono interior_subset) (hginj.mono interior_subset)
    have hsub : Function.invFunOn u P '' interior (u '' P) ⊆ interior P := by
      refine interior_maximal ?_ hopen
      rintro _ ⟨y, hy, rfl⟩
      exact hgmaps (interior_subset hy)
    intro y hy
    exact ⟨Function.invFunOn u P y, hsub ⟨y, hy, rfl⟩, hug y (interior_subset hy)⟩

theorem IsPLHomeomorphInto.image_frontier_of_isCompact [T2Space M₁]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₁}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsCompact P) :
    u '' frontier P = frontier (u '' P) := by
  have hclosed : IsClosed (u '' P) := (hP.image_of_continuousOn hu.continuousOn).isClosed
  rw [hP.isClosed.frontier_eq, hu.injOn.image_sdiff_subset interior_subset, hu.image_interior,
    ← hclosed.frontier_eq]

end InvarianceOfDomain

section Cell

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem IsPLCellOn.boundary_subset {d : ℕ} {S B : Set M₁} (h : IsPLCellOn d S B) : B ⊆ S := by
  obtain ⟨P, r, u, hr, -, hS, hB⟩ := h
  rw [hS, hB]
  refine image_mono ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hr.bijOn.mapsTo hy.1

theorem IsPLCellOn.dim_eq {d d' : ℕ} {S B B' : Set M₁} (h : IsPLCellOn d S B)
    (h' : IsPLCellOn d' S B') : d = d' := by
  obtain ⟨P₁, r₁, u₁, hr₁, hu₁, hS₁, -⟩ := h
  obtain ⟨P₂, r₂, u₂, hr₂, hu₂, hS₂, -⟩ := h'
  have hb₁ : IsPLBall d P₁ := ⟨r₁, hr₁⟩
  have hb₂ : IsPLBall d' P₂ := ⟨r₂, hr₂⟩
  have himg : u₁ '' P₁ = u₂ '' P₂ := by rw [← hS₁, ← hS₂]
  have htr := hu₁.isPLHomeomorphOn_transition hb₁.isPolyhedron hu₂ himg
  exact hb₁.dim_eq (hb₂.of_isPLHomeomorphOn htr.symm)

theorem IsPLCellOn.boundary_eq {d d' : ℕ} {S B B' : Set M₁} (h : IsPLCellOn d S B)
    (h' : IsPLCellOn d' S B') : B = B' := by
  obtain rfl := h.dim_eq h'
  by_cases hd : d = 0
  · subst hd
    obtain ⟨P₁, r₁, u₁, -, -, -, hB₁⟩ := h
    obtain ⟨P₂, r₂, u₂, -, -, -, hB₂⟩ := h'
    rw [hB₁, hB₂, stdSimplexBoundary_zero]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    obtain ⟨P₁, r₁, u₁, hr₁, hu₁, hS₁, hB₁⟩ := h
    obtain ⟨P₂, r₂, u₂, hr₂, hu₂, hS₂, hB₂⟩ := h'
    have hb₁ : IsPLBall (m + 1) P₁ := ⟨r₁, hr₁⟩
    have himg : u₁ '' P₁ = u₂ '' P₂ := by rw [← hS₁, ← hS₂]
    have htr := hu₁.isPLHomeomorphOn_transition hb₁.isPolyhedron hu₂ himg
    have hcongr := IsPLHomeomorphOn.image_stdSimplexBoundary_congr (m := m) (hr₁.trans htr) hr₂
    have hsub : r₁ '' stdSimplexBoundary (m + 1) ⊆ P₁ := by
      rintro _ ⟨y, hy, rfl⟩
      exact hr₁.bijOn.mapsTo hy.1
    have hval : ∀ x ∈ P₁, u₂ (Function.invFunOn u₂ P₂ (u₁ x)) = u₁ x := fun x hx =>
      hu₂.injOn.bijOn_image.invOn_invFunOn.2 (himg ▸ ⟨x, hx, rfl⟩)
    have hstep : u₂ '' ((Function.invFunOn u₂ P₂ ∘ u₁) '' (r₁ '' stdSimplexBoundary (m + 1)))
        = u₁ '' (r₁ '' stdSimplexBoundary (m + 1)) := by
      rw [← image_comp]
      exact image_congr fun x hx => hval x (hsub hx)
    rw [hB₁, hB₂, ← hcongr, image_comp, hstep]

theorem IsPLCellOn.boundary_eq_frontier [T2Space M₁] {S B : Set M₁} (h : IsPLCellOn 3 S B) :
    B = frontier S := by
  obtain ⟨P, r, u, hr, hu, hS, hB⟩ := h
  have hball : IsPLBall 3 P := ⟨r, hr⟩
  have hfr : r '' stdSimplexBoundary 3 = frontier P :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr
  rw [hB, hfr, hu.image_frontier_of_isCompact hball.isPolyhedron.isCompact, hS]

theorem IsPLCellOn.sdiff_boundary_eq_interior {S B : Set M₁}
    (h : IsPLCellOn 3 S B) : S \ B = interior S := by
  obtain ⟨P, r, u, hr, hu, hS, hB⟩ := h
  have hball : IsPLBall 3 P := ⟨r, hr⟩
  have hclosed : IsClosed P := hball.isPolyhedron.isClosed
  have hfr : r '' stdSimplexBoundary 3 = frontier P :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr
  have hdiff : P \ frontier P = interior P := by
    rw [hclosed.frontier_eq, Set.sdiff_sdiff_cancel_left interior_subset]
  rw [hS, hB, hfr, ← hu.injOn.image_sdiff_subset hclosed.frontier_subset, hdiff]
  exact hu.image_interior

theorem IsPLCellOn.image {d : ℕ} {S B : Set M₁} (h : IsPLCellOn d S B) {G : M₁ → M₂}
    (hG : IsPLHomeomorphInto 3 G S) : IsPLCellOn d (G '' S) (G '' B) := by
  obtain ⟨P, r, u, hr, hu, hS, hB⟩ := h
  subst hS
  subst hB
  exact ⟨P, r, G ∘ u, hr, hu.comp_of_image_eq hG, (image_comp G u P).symm,
    (image_comp G u (r '' stdSimplexBoundary d)).symm⟩

theorem IsPLCellOn.image_boundary_interior [T2Space M₂] {S B : Set M₁} (h : IsPLCellOn 3 S B)
    {G : M₁ → M₂} (hG : IsPLHomeomorphInto 3 G S) :
    G '' B = frontier (G '' S) ∧ G '' (S \ B) = interior (G '' S) := by
  refine ⟨(h.image hG).boundary_eq_frontier, ?_⟩
  rw [hG.injOn.image_sdiff_subset h.boundary_subset]
  exact (h.image hG).sdiff_boundary_eq_interior

end Cell

section Inhabitant

theorem isPLCellOn_id_of_isPLBall {d : ℕ} {P : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) P) :
    IsPLCellOn (M := EuclideanSpace ℝ (Fin 3)) d P (r '' stdSimplexBoundary d) :=
  ⟨P, r, id, hr, isPLHomeomorphInto_id_of_isPolyhedron (IsPLBall.isPolyhedron ⟨r, hr⟩),
    (image_id P).symm, (image_id _).symm⟩

theorem nonempty_stdSimplexBoundary_of_pos {d : ℕ} (hd : 0 < d) :
    (stdSimplexBoundary d).Nonempty := by
  have hlt : 1 < d + 1 := by omega
  have hne : (⟨1, hlt⟩ : Fin (d + 1)) ≠ 0 := by
    simp [Fin.ext_iff]
  exact ⟨Pi.single (0 : Fin (d + 1)) 1, Convexity.StdSimplex.single_mem_coordinateSet ℝ 0, ⟨1, hlt⟩,
    Pi.single_eq_of_ne hne 1⟩

theorem exists_isPLCellOn_of_le_three (d : ℕ) (hd : d ≤ 3) :
    ∃ S B : Set (EuclideanSpace ℝ (Fin 3)), IsPLCellOn d S B ∧ (0 < d → B.Nonempty) := by
  classical
  obtain ⟨J, hJ, hcard⟩ :
      ∃ J : Finset (Fin 5), (J.Nonempty ∧ ¬ ({3, 4} : Finset (Fin 5)) ⊆ J) ∧ J.card = d + 1 := by
    have h : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨{0}, by decide, by decide⟩
    · exact ⟨{0, 1}, by decide, by decide⟩
    · exact ⟨{0, 1, 2}, by decide, by decide⟩
    · exact ⟨{0, 1, 2, 3}, by decide, by decide⟩
  have hdim : bentTetrahedraDim ⟨J, hJ⟩ = d := by
    simp only [bentTetrahedraDim, hcard]
    omega
  have hball : IsPLBall d (bentTetrahedraSourceCell ⟨J, hJ⟩) :=
    hdim ▸ isPLBall_bentTetrahedraSourceCell ⟨J, hJ⟩
  obtain ⟨r, hr⟩ := hball
  refine ⟨bentTetrahedraSourceCell ⟨J, hJ⟩, r '' stdSimplexBoundary d,
    isPLCellOn_id_of_isPLBall hr, fun hpos => ?_⟩
  exact (nonempty_stdSimplexBoundary_of_pos hpos).image r

end Inhabitant

end DifferentialGeometry.Topology.PiecewiseLinear
