import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanProtectedComplex
import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanQuotient
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementRestriction
import DifferentialGeometry.Topology.Engulfing.Local.Charts.LocalOptimalApproximation
import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexInterior

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped ContinuousMap

section Geometry

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [DecidableEq F] in
theorem exists_finite_polyhedral_neighborhood {A U : Set F}
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ B : SimplicialComplex ℝ F, B.faces.Finite ∧ A ⊆ B.space ∧ B.space ⊆ U ∧
      ∀ s ∈ B.faces, s.card ≤ Module.finrank ℝ F + 1 := by
  classical
  obtain ⟨K, _, hK, _, hAK, _⟩ := exists_finite_convex_complex_containing_bounded
    (⊥ : SimplicialComplex ℝ F) finite_empty A hA.isBounded
  have hdim : ∀ s ∈ K.faces, s.card ≤ Module.finrank ℝ F + 1 := by
    intro s hs
    simpa only [Fintype.card_coe] using (K.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  obtain ⟨P, _, B, _, _, _, hPdim, _, _, _, _, hB, hBP, hBU, hAB, _⟩ :=
    exists_subcomplex_neighborhood_preserving K ⊥ hK (empty_subset _) hA
      (fun x hx => interior_subset (hAK (Or.inr hx))) hU hAU hdim
  exact ⟨B, hB, hAB, hBU, fun s hs => hPdim s (hBP hs)⟩

omit [DecidableEq F] in
theorem exists_finite_complex_between_balls (c : F) {r R : ℝ} (h : r < R) :
    ∃ B : SimplicialComplex ℝ F, B.faces.Finite ∧
      Metric.closedBall c r ⊆ B.space ∧ B.space ⊆ Metric.ball c R := by
  classical
  obtain ⟨B, hB, hin, hout, _⟩ := exists_finite_polyhedral_neighborhood
    (isCompact_closedBall c r) Metric.isOpen_ball (Metric.closedBall_subset_ball h)
  exact ⟨B, hB, hin, hout⟩

omit [DecidableEq E] [DecidableEq F] in
theorem exists_local_saturated_protected_complex
    (C H : SimplicialComplex ℝ E) (hC : C.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ C.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ C.faces, InjOn f (convexHull ℝ (s : Set E)))
    (B T : SimplicialComplex ℝ F) (hB : B.faces.Finite) (hT : T.faces.Finite)
    {d p q : ℕ} (hd : ∀ s ∈ C.faces, s.card ≤ d + 1)
    (hHd : ∀ s ∈ H.faces, s.card ≤ p + 1) (hTd : ∀ t ∈ T.faces, t.card ≤ q)
    (hqp : q ≤ p + 1) :
    ∃ G D R P : SimplicialComplex ℝ E,
      G.faces.Finite ∧ G.space = C.space ∧ simplicialRefines G C ∧
      (∀ s ∈ G.faces, s.card ≤ d + 1) ∧ D.faces.Finite ∧ D.faces ⊆ G.faces ∧
      D.space = C.space ∩ f ⁻¹' ((f '' (C ⊓ H).space ∩ B.space) ∪ T.space) ∧
      (∀ s ∈ D.faces, s.card ≤ p + 1) ∧
      R.faces ⊆ D.faces ∧ P.faces ⊆ D.faces ∧ D.faces = R.faces ∪ P.faces ∧
      R.space = C.space ∩ f ⁻¹' (f '' (C ⊓ H).space ∩ B.space) ∧
      P.space = C.space ∩ f ⁻¹' T.space ∧ (∀ s ∈ P.faces, s.card ≤ q) := by
  classical
  obtain ⟨T₀, hT₀, hT₀space, hT₀dim, -⟩ := exists_image_complex_of_facewise_affine
    (C ⊓ H) (hC.subset (fun _ hs => hs.1)) f (fun s hs => hf s hs.1)
    (fun s hs => hHd s hs.2)
  obtain ⟨A, B', hA, -, -, hAdim, hB', hB'A, hB'space, -⟩ :=
    exists_common_triangulation T₀ B hT₀ hB hT₀dim
  obtain ⟨G, D, R, P, hG, hGspace, href, hGdim, hD, hDG, hDspace, hDdim,
    hRD, hPD, hfaces, hRspace, hPspace, hPdim, -⟩ :=
    exists_saturated_protected_complex C hC f hf hinj B' T hB' hT hd
      (fun s hs => hAdim s (hB'A hs)) hTd hqp
  rw [hB'space, hT₀space] at hDspace hRspace
  exact ⟨G, D, R, P, hG, hGspace, href, hGdim, hD, hDG, hDspace, hDdim,
    hRD, hPD, hfaces, hRspace, hPspace, hPdim⟩

omit [DecidableEq E] [DecidableEq F] in
theorem exists_global_local_saturation [FiniteDimensional ℝ E]
    (K L C H : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hCK : C.faces ⊆ K.faces) (hHK : H.faces ⊆ K.faces)
    (f : E → F)
    (hf : ∀ s ∈ C.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ C.faces, InjOn f (convexHull ℝ (s : Set E)))
    (B T : SimplicialComplex ℝ F) (hB : B.faces.Finite) (hT : T.faces.Finite)
    {d p q : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (hHd : ∀ s ∈ H.faces, s.card ≤ p + 1) (hTd : ∀ t ∈ T.faces, t.card ≤ q)
    (hqp : q ≤ p + 1) :
    ∃ G L' D R P : SimplicialComplex ℝ E,
      G.faces.Finite ∧ G.space = K.space ∧ simplicialRefines G K ∧
      (∀ s ∈ G.faces, s.card ≤ d + 1) ∧
      L'.faces ⊆ G.faces ∧ L'.space = L.space ∧ simplicialRefines L' L ∧
      D.faces ⊆ G.faces ∧ R.faces ⊆ G.faces ∧ P.faces ⊆ G.faces ∧
      D.space = C.space ∩ f ⁻¹' ((f '' (C.space ∩ H.space) ∩ B.space) ∪ T.space) ∧
      R.space = H.space ∪ (C.space ∩ f ⁻¹' (f '' (C.space ∩ H.space) ∩ B.space)) ∧
      P.space = C.space ∩ f ⁻¹' T.space ∧
      (∀ s ∈ D.faces, s.card ≤ p + 1) ∧
      (∀ s ∈ R.faces, s.card ≤ p + 1) ∧ (∀ s ∈ P.faces, s.card ≤ q) ∧
      (∀ s ∈ D.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) ∧
      (∀ s ∈ D.faces, InjOn f (convexHull ℝ (s : Set E))) ∧
      ∃ J : SimplicialComplex ℝ E, J.faces ⊆ G.faces ∧ J.space = C.space ∧
        (∀ s ∈ J.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) ∧
        (∀ s ∈ J.faces, InjOn f (convexHull ℝ (s : Set E))) := by
  classical
  obtain ⟨G₀, D₀, R₀, P₀, hG₀, hG₀space, hG₀ref, -, -, hD₀G₀, hD₀space,
    hD₀dim, hR₀D₀, hP₀D₀, -, hR₀space, hP₀space, hP₀dim⟩ :=
    exists_local_saturated_protected_complex C H (hK.subset hCK) f hf hinj B T hB hT
      (fun s hs => hd s (hCK hs)) hHd hTd hqp
  have hG₀K : G₀.space ⊆ K.space := hG₀space.subset.trans (subcomplex_space_subset K C hCK)
  obtain ⟨G, J, hG, hGspace, hGref, hGdim, -, hJG, hJspace, hJref⟩ :=
    exists_subdivision_containing_complex K G₀ hK hG₀ hG₀K hd
  let L' := complexRestriction G L
  let H' := complexRestriction G H
  let D := complexRestriction J D₀
  let R' := complexRestriction J R₀
  let P := complexRestriction J P₀
  have hL'G : L'.faces ⊆ G.faces := complexRestriction_faces_subset _ _
  have hH'G : H'.faces ⊆ G.faces := complexRestriction_faces_subset _ _
  have hDG : D.faces ⊆ G.faces := (complexRestriction_faces_subset J D₀).trans hJG
  have hR'G : R'.faces ⊆ G.faces := (complexRestriction_faces_subset J R₀).trans hJG
  have hPG : P.faces ⊆ G.faces := (complexRestriction_faces_subset J P₀).trans hJG
  have hL'space : L'.space = L.space := complexRestriction_space_of_refines _ _ _ hGref hGspace hLK
  have hH'space : H'.space = H.space := complexRestriction_space_of_refines _ _ _ hGref hGspace hHK
  have hDspace : D.space = D₀.space :=
    complexRestriction_space_of_refines J G₀ D₀ hJref hJspace hD₀G₀
  have hR'space : R'.space = R₀.space :=
    complexRestriction_space_of_refines J G₀ R₀ hJref hJspace (hR₀D₀.trans hD₀G₀)
  have hPspace : P.space = P₀.space :=
    complexRestriction_space_of_refines J G₀ P₀ hJref hJspace (hP₀D₀.trans hD₀G₀)
  have hCHspace : (C ⊓ H).space = C.space ∩ H.space := subcomplex_inf_space K C H hCK hHK
  rw [hCHspace] at hD₀space hR₀space
  let R := subcomplexPair G H' R' hH'G hR'G
  have hDref : simplicialRefines D C := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hJref s hs.1
    obtain ⟨u, hu, htu⟩ := hG₀ref t ht
    exact ⟨u, hu, hst.trans htu⟩
  refine ⟨G, L', D, R, P, hG, hGspace, hGref, hGdim, hL'G, hL'space,
    complexRestriction_refines_right _ _, hDG, subcomplexPair_faces_subset _ _ _ _ _, hPG,
    hDspace.trans hD₀space, ?_, hPspace.trans hP₀space, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show R.space = H'.space ∪ R'.space from subcomplexPair_space _ _ _ _ _,
      hH'space, hR'space, hR₀space]
  · exact (complexRestriction_refines_right J D₀).face_card_le_bound hD₀dim
  · intro s hs
    rw [show R.faces = H'.faces ∪ R'.faces from subcomplexPair_faces _ _ _ _ _] at hs
    rcases hs with hs | hs
    · exact (complexRestriction_refines_right G H).face_card_le_bound hHd s hs
    · exact (complexRestriction_refines_right J R₀).face_card_le_bound
        (fun t ht => hD₀dim t (hR₀D₀ ht)) s hs
  · exact (complexRestriction_refines_right J P₀).face_card_le_bound hP₀dim
  · intro s hs
    obtain ⟨t, ht, hst⟩ := hDref s hs
    obtain ⟨A, hA⟩ := hf t ht
    exact ⟨A, hA.mono hst⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := hDref s hs
    exact (hinj t ht).mono hst
  · refine ⟨J, hJG, hJspace.trans hG₀space, ?_, ?_⟩
    · intro s hs
      obtain ⟨t, ht, hst⟩ := hJref s hs
      obtain ⟨u, hu, htu⟩ := hG₀ref t ht
      obtain ⟨A, hA⟩ := hf u hu
      exact ⟨A, hA.mono (hst.trans htu)⟩
    · intro s hs
      obtain ⟨t, ht, hst⟩ := hJref s hs
      obtain ⟨u, hu, htu⟩ := hG₀ref t ht
      exact (hinj u hu).mono (hst.trans htu)

omit [DecidableEq F] [FiniteDimensional ℝ F] in
omit [DecidableEq E] in
theorem exists_chart_affine_on_source_faces {M : Type*} [TopologicalSpace M]
    (K C : SimplicialComplex ℝ E) (hCK : C.faces ⊆ K.faces)
    (a : E → F)
    (ha : ∀ s ∈ C.faces, ∃ A : E →ᵃ[ℝ] F, EqOn a A (convexHull ℝ (s : Set E)))
    (f : C(K.space, M)) (e : M → F) (U : Set M)
    (hcore : ∀ x : K.space, f x ∈ U → x ∈ interior (Subtype.val ⁻¹' C.space))
    (hcoords : ∀ x : K.space, f x ∈ U → e (f x) = a x.1) :
    ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F,
      ∀ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) → f x ∈ U → e (f x) = A x.1 := by
  classical
  intro s hs
  by_cases hmeet : ∃ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ f x ∈ U
  · obtain ⟨x, hx, hxU⟩ := hmeet
    have hsC := face_mem_subcomplex_of_mem_interior K C hCK hs hx (hcore x hxU)
    obtain ⟨A, hA⟩ := ha s hsC
    exact ⟨A, fun y hy hyU => (hcoords y hyU).trans (hA hy)⟩
  · exact ⟨0, fun x hx hxU => (hmeet ⟨x, hx, hxU⟩).elim⟩

end Geometry

section Sets

variable {Z M F : Type*} [TopologicalSpace M] [TopologicalSpace F]

def localProtectedSet (a : Z → F) (C H : Set Z) (B T : Set F) : Set Z :=
  C ∩ a ⁻¹' ((a '' (C ∩ H) ∩ B) ∪ T)

def localCoveredSet (a : Z → F) (C H : Set Z) (B : Set F) : Set Z :=
  H ∪ (C ∩ a ⁻¹' (a '' (C ∩ H) ∩ B))

variable (f : Z → M) (a : Z → F) (e : OpenPartialHomeomorph M F)
    {C H : Set Z} {B T : Set F}
    (hcoords : ∀ x ∈ C, f x ∈ e.source ∧ e (f x) = a x)
    (hcovers : ∀ x, f x ∈ e.source → e (f x) ∈ B → x ∈ C)
    (hTB : T ⊆ B)

include hcoords hTB in
theorem localProtectedSet_image_subset :
    f '' localProtectedSet a C H B T ⊆ e.symm '' B := by
  rintro _ ⟨x, hx, rfl⟩
  have hB : a x ∈ B := hx.2.elim (fun h => h.2) (fun h => hTB h)
  refine ⟨a x, hB, ?_⟩
  rw [← (hcoords x hx.1).2, e.left_inv (hcoords x hx.1).1]

include hcoords hcovers hTB in
theorem localProtectedSet_saturated :
    ∀ x ∈ localProtectedSet a C H B T, ∀ y, f y = f x →
      y ∈ localProtectedSet a C H B T := by
  intro x hx y hxy
  have hxB : a x ∈ B := hx.2.elim (fun h => h.2) (fun h => hTB h)
  have hySource : f y ∈ e.source := hxy ▸ (hcoords x hx.1).1
  have hye : e (f y) = a x := (congrArg e hxy).trans (hcoords x hx.1).2
  have hyC : y ∈ C := hcovers y hySource (hye.symm ▸ hxB)
  have heq : a y = a x := (hcoords y hyC).2.symm.trans hye
  refine ⟨hyC, ?_⟩
  change a y ∈ (a '' (C ∩ H) ∩ B) ∪ T
  rw [heq]
  exact hx.2

include hcoords hTB in
theorem localProtectedSet_saturated_on {L : Set Z}
    (hLcovers : ∀ y ∈ L, f y ∈ e.source → e (f y) ∈ B → y ∈ C) :
    ∀ x ∈ localProtectedSet a C H B T, ∀ y ∈ L, f y = f x →
      y ∈ localProtectedSet a C H B T := by
  intro x hx y hyL hxy
  have hxB : a x ∈ B := hx.2.elim (fun h => h.2) (fun h => hTB h)
  have hySource : f y ∈ e.source := hxy ▸ (hcoords x hx.1).1
  have hye : e (f y) = a x := (congrArg e hxy).trans (hcoords x hx.1).2
  have hyC : y ∈ C := hLcovers y hyL hySource (hye.symm ▸ hxB)
  have heq : a y = a x := (hcoords y hyC).2.symm.trans hye
  refine ⟨hyC, ?_⟩
  change a y ∈ (a '' (C ∩ H) ∩ B) ∪ T
  rw [heq]
  exact hx.2

include hcoords in
theorem localCoveredSet_image_subset : f '' localCoveredSet a C H B ⊆ f '' H := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with hxH | ⟨hxC, ⟨y, hy, hya⟩, -⟩
  · exact mem_image_of_mem f hxH
  · refine ⟨y, hy.2, ?_⟩
    have heq : e (f y) = e (f x) :=
      (hcoords y hy.1).2.trans (hya.trans (hcoords x hxC).2.symm)
    exact (e.left_inv (hcoords y hy.1).1).symm.trans
      ((congrArg e.symm heq).trans (e.left_inv (hcoords x hxC).1))

include hcoords in
theorem localCoveredSet_image_eq : f '' localCoveredSet a C H B = f '' H :=
  Subset.antisymm (localCoveredSet_image_subset f a e hcoords)
    (image_mono (fun _ hx => Or.inl hx))

include hcoords in
theorem localColumnSet_image_eq (hTimage : T ⊆ a '' C) :
    f '' (C ∩ a ⁻¹' T) = e.symm '' T := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨a x, hx.2, ((congrArg e.symm (hcoords x hx.1).2).symm).trans
      (e.left_inv (hcoords x hx.1).1)⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨x, hx, hxt⟩ := hTimage ht
    refine ⟨x, ⟨hx, ?_⟩, ?_⟩
    · change a x ∈ T
      rwa [hxt]
    · exact (e.left_inv (hcoords x hx).1).symm.trans
        (congrArg e.symm ((hcoords x hx).2.trans hxt))

include hcoords in
theorem localTargetSet_image_eq (hTimage : T ⊆ a '' C) :
    f '' (localCoveredSet a C H B ∪ (C ∩ a ⁻¹' T)) = f '' H ∪ e.symm '' T := by
  rw [image_union, localCoveredSet_image_eq f a e hcoords,
    localColumnSet_image_eq f a e hcoords hTimage]

include hcoords in
theorem localTargetSet_attachment {X : Set M} {σ ρ : Set F}
    (hTimage : T ⊆ a '' C) (hTσ : T ⊆ σ) (hσ : σ ⊆ e.target)
    (hattach : e.symm ⁻¹' (X ∪ f '' H) ∩ σ ⊆ ρ ∪ T) :
    e.symm ⁻¹' (X ∪ f '' (localCoveredSet a C H B ∪ (C ∩ a ⁻¹' T))) ∩ σ ⊆ ρ ∪ T := by
  rw [localTargetSet_image_eq f a e hcoords hTimage]
  rintro x ⟨hx, hxσ⟩
  rcases hx with hxX | hxH | ⟨t, ht, htx⟩
  · exact hattach ⟨Or.inl hxX, hxσ⟩
  · exact hattach ⟨Or.inr hxH, hxσ⟩
  · have heq : t = x := e.symm.injOn (hσ (hTσ ht)) (hσ hxσ) htx
    exact Or.inr (heq ▸ ht)

include hcoords in
theorem localTargetSet_roof_columns {U : Set Z} {σ ρ : Set F}
    (hTimage : T ⊆ a '' C) (hTσ : T ⊆ σ) (hρσ : ρ ⊆ σ)
    (hroof : e.symm '' ρ ⊆ f '' H) (hbuffer : f ⁻¹' (e.symm '' σ) ⊆ U) :
    e.symm '' (ρ ∪ T) ⊆
      f '' ((localCoveredSet a C H B ∪ (C ∩ a ⁻¹' T)) ∩ U) := by
  intro y hy
  have hyσ : y ∈ e.symm '' σ := image_mono (union_subset hρσ hTσ) hy
  have hyTarget : y ∈ f '' (localCoveredSet a C H B ∪ (C ∩ a ⁻¹' T)) := by
    rw [localTargetSet_image_eq f a e hcoords hTimage]
    rcases hy with ⟨t, ht | ht, rfl⟩
    · exact Or.inl (hroof (mem_image_of_mem e.symm ht))
    · exact Or.inr (mem_image_of_mem e.symm ht)
  obtain ⟨x, hx, rfl⟩ := hyTarget
  exact ⟨x, ⟨hx, hbuffer hyσ⟩, rfl⟩

include hcoords hcovers in
theorem local_target_inter_subset_protected {U : Set Z}
    (hU : ∀ x ∈ U, f x ∈ e.source ∧ e (f x) ∈ B) :
    (localCoveredSet a C H B ∪ (C ∩ a ⁻¹' T)) ∩ U ⊆ localProtectedSet a C H B T := by
  rintro x ⟨hx, hxU⟩
  have hxC : x ∈ C := hcovers x (hU x hxU).1 (hU x hxU).2
  rcases hx with (hxH | hxR) | hxP
  · exact ⟨hxC, Or.inl ⟨mem_image_of_mem a ⟨hxC, hxH⟩,
      (hcoords x hxC).2 ▸ (hU x hxU).2⟩⟩
  · exact ⟨hxR.1, Or.inl hxR.2⟩
  · exact ⟨hxP.1, Or.inr hxP.2⟩

include hcoords in
theorem local_target_inter_subset_protected_of_covers_covered {U : Set Z}
    (hHcovers : ∀ x ∈ H, f x ∈ e.source → e (f x) ∈ B → x ∈ C)
    (hU : ∀ x ∈ U, f x ∈ e.source ∧ e (f x) ∈ B) :
    (localCoveredSet a C H B ∪ (C ∩ a ⁻¹' T)) ∩ U ⊆ localProtectedSet a C H B T := by
  rintro x ⟨hx, hxU⟩
  rcases hx with (hxH | hxR) | hxP
  · have hxC := hHcovers x hxH (hU x hxU).1 (hU x hxU).2
    exact ⟨hxC, Or.inl ⟨mem_image_of_mem a ⟨hxC, hxH⟩,
      (hcoords x hxC).2 ▸ (hU x hxU).2⟩⟩
  · exact ⟨hxR.1, Or.inl hxR.2⟩
  · exact ⟨hxP.1, Or.inr hxP.2⟩

include hcoords in
theorem local_target_inter_subset_protected_of_local_cover {U : Set Z}
    (hHlocal : H ∩ U ⊆ C)
    (hU : ∀ x ∈ U, f x ∈ e.source ∧ e (f x) ∈ B) :
    (localCoveredSet a C H B ∪ (C ∩ a ⁻¹' T)) ∩ U ⊆ localProtectedSet a C H B T := by
  rintro x ⟨hx, hxU⟩
  rcases hx with (hxH | hxR) | hxP
  · have hxC := hHlocal ⟨hxH, hxU⟩
    exact ⟨hxC, Or.inl ⟨mem_image_of_mem a ⟨hxC, hxH⟩,
      (hcoords x hxC).2 ▸ (hU x hxU).2⟩⟩
  · exact ⟨hxR.1, Or.inl hxR.2⟩
  · exact ⟨hxP.1, Or.inr hxP.2⟩

omit [TopologicalSpace M] [TopologicalSpace F] in
theorem eqOn_local_model_of_saturated_fixed {f g : Z → M} {a : Z → F}
    {C H L S : Set Z} {B T : Set F}
    (hL : EqOn g f L) (hS : EqOn g f S)
    (hD : EqOn g f (localProtectedSet a C H B T))
    (hC : C ⊆ (L ∪ H) ∪ S) (hCH : a '' ((C \ L) ∩ H) ⊆ B) : EqOn g f C := by
  intro x hx
  by_cases hxL : x ∈ L
  · exact hL hxL
  rcases hC hx with (hxL | hxH) | hxS
  · exact hL hxL
  · exact hD ⟨hx, Or.inl ⟨mem_image_of_mem a ⟨hx, hxH⟩,
      hCH (mem_image_of_mem a ⟨⟨hx, hxL⟩, hxH⟩)⟩⟩
  · exact hS hxS

end Sets

section Transport

variable {Z E M F : Type*} [TopologicalSpace M] [TopologicalSpace F]

omit [TopologicalSpace F] in
theorem image_local_inter_preimage (z : Z → E) (a : E → F) {C H : Set E}
    (hC : C ⊆ range z) :
    (a ∘ z) '' (z ⁻¹' C ∩ z ⁻¹' H) = a '' (C ∩ H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨z x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, rfl⟩ := hC hx.1
    exact ⟨w, hx, rfl⟩

omit [TopologicalSpace F] in
theorem localProtectedSet_preimage (z : Z → E) (a : E → F) {C H : Set E}
    {B T : Set F} (hC : C ⊆ range z) :
    localProtectedSet (a ∘ z) (z ⁻¹' C) (z ⁻¹' H) B T =
      z ⁻¹' localProtectedSet a C H B T := by
  rw [localProtectedSet, image_local_inter_preimage z a hC]
  rfl

omit [TopologicalSpace F] in
theorem localCoveredSet_preimage (z : Z → E) (a : E → F) {C H : Set E}
    {B : Set F} (hC : C ⊆ range z) :
    localCoveredSet (a ∘ z) (z ⁻¹' C) (z ⁻¹' H) B =
      z ⁻¹' localCoveredSet a C H B := by
  rw [localCoveredSet, image_local_inter_preimage z a hC]
  rfl

theorem chart_saturation_properties
    (z : Z → E) (a : E → F) (f : Z → M) (e : OpenPartialHomeomorph M F)
    {C H D R P : Set E} {B T : Set F}
    (hC : C ⊆ range z)
    (hD : D = localProtectedSet a C H B T)
    (hR : R = localCoveredSet a C H B) (hP : P = C ∩ a ⁻¹' T)
    (hcoords : ∀ x, z x ∈ C → f x ∈ e.source ∧ e (f x) = a (z x))
    (hcovers : ∀ x, f x ∈ e.source → e (f x) ∈ B → z x ∈ C)
    (hTB : T ⊆ B) :
    (∀ x, z x ∈ D → ∀ y, f y = f x → z y ∈ D) ∧
    f '' (z ⁻¹' D) ⊆ e.symm '' B ∧
    f '' (z ⁻¹' R) ⊆ f '' (z ⁻¹' H) ∧
    (∀ U : Set Z, (∀ x ∈ U, f x ∈ e.source ∧ e (f x) ∈ B) →
      (z ⁻¹' (R ∪ P)) ∩ U ⊆ z ⁻¹' D) := by
  have hD' : z ⁻¹' D = localProtectedSet (a ∘ z) (z ⁻¹' C) (z ⁻¹' H) B T := by
    rw [hD, localProtectedSet_preimage z a hC]
  have hR' : z ⁻¹' R = localCoveredSet (a ∘ z) (z ⁻¹' C) (z ⁻¹' H) B := by
    rw [hR, localCoveredSet_preimage z a hC]
  have hcoords' : ∀ x ∈ z ⁻¹' C, f x ∈ e.source ∧ e (f x) = (a ∘ z) x := hcoords
  have hcovers' : ∀ x, f x ∈ e.source → e (f x) ∈ B → x ∈ z ⁻¹' C := hcovers
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hxy
    have hx' : x ∈ localProtectedSet (a ∘ z) (z ⁻¹' C) (z ⁻¹' H) B T := by
      rw [← hD']
      exact hx
    have hy := localProtectedSet_saturated f (a ∘ z) e hcoords' hcovers' hTB x hx' y hxy
    rw [← hD'] at hy
    exact hy
  · rw [hD']
    exact localProtectedSet_image_subset f (a ∘ z) e hcoords' hTB
  · rw [hR']
    exact localCoveredSet_image_subset f (a ∘ z) e hcoords'
  · intro U hU
    rw [preimage_union, hR', hP, hD']
    exact local_target_inter_subset_protected f (a ∘ z) e hcoords' hcovers' hU

end Transport

end DifferentialGeometry.Topology.Engulfing
