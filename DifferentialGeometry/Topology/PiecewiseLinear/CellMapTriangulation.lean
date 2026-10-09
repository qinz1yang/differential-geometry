/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import Mathlib.Analysis.Convex.Caratheodory

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
open Classical in
theorem isPolyhedron_convexHull_finset (s : Finset E) :
    IsPolyhedron (convexHull ℝ (s : Set E)) := by
  let T : Finset (Finset E) :=
    s.powerset.filter fun (t : Finset E) => AffineIndependent ℝ (fun x : {x : E // x ∈ t} => x.1)
  have heq : convexHull ℝ (s : Set E) = ⋃ t : T, convexHull ℝ ((t : Finset E) : Set E) := by
    ext x
    constructor
    · intro hx
      rw [convexHull_eq_union] at hx
      simp only [mem_iUnion] at hx
      obtain ⟨t, hts, hind, hxt⟩ := hx
      exact mem_iUnion.mpr
        ⟨⟨t, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, hind⟩⟩, hxt⟩
    · intro hx
      obtain ⟨t, hxt⟩ := mem_iUnion.mp hx
      exact convexHull_mono (Finset.mem_powerset.mp (Finset.mem_filter.mp t.2).1) hxt
  rw [heq]
  exact IsPolyhedron.iUnion fun t : T =>
    isPolyhedron_convexHull_of_affineIndependent (t : Finset E) (Finset.mem_filter.mp t.2).2

open Classical in
theorem IsPolyhedron.image_affineMap {P : Set E} (hP : IsPolyhedron P) (A : E →ᵃ[ℝ] F) :
    IsPolyhedron (A '' P) := by
  obtain ⟨K, hfin, rfl⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  have heq : A '' K.space = ⋃ s : K.faces, convexHull ℝ (((s : Finset E).image A) : Set F) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
      apply mem_iUnion.mpr
      refine ⟨⟨s, hs⟩, ?_⟩
      rw [Finset.coe_image, ← A.image_convexHull]
      exact mem_image_of_mem A hxs
    · intro hy
      obtain ⟨s, hys⟩ := mem_iUnion.mp hy
      rw [Finset.coe_image, ← A.image_convexHull] at hys
      obtain ⟨x, hxs, rfl⟩ := hys
      exact mem_image_of_mem A (K.convexHull_subset_space s.2 hxs)
  rw [heq]
  exact IsPolyhedron.iUnion fun s : K.faces =>
    isPolyhedron_convexHull_finset ((s : Finset E).image A)

open Classical in
theorem IsPiecewiseAffineOn.isPolyhedron_image {P : Set E} {f : E → F}
    (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P) : IsPolyhedron (f '' P) := by
  obtain ⟨K, hfin, rfl⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  obtain ⟨K', hK', hfin', hfaces⟩ := hf.exists_isSubdivision_affineOn_faces K
  let _ : Finite K'.faces := hfin'.to_subtype
  choose A hA using hfaces
  have heq : f '' K.space =
      ⋃ s : K'.faces, A s s.2 '' convexHull ℝ ((s : Finset E) : Set E) := by
    rw [← hK'.space_eq]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hxs⟩ := K'.mem_space_iff.mp hx
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, x, hxs, (hA s hs hxs).symm⟩
    · intro hy
      obtain ⟨s, x, hxs, rfl⟩ := mem_iUnion.mp hy
      exact ⟨x, K'.convexHull_subset_space s.2 hxs, hA s s.2 hxs⟩
  rw [heq]
  exact IsPolyhedron.iUnion fun s : K'.faces =>
    (isPolyhedron_convexHull_of_affineIndependent s (K'.indep s.2)).image_affineMap (A s s.2)

section Arrangements

variable {ι κ : Type*} {l : ι → E →ᵃ[ℝ] ℝ} {m : κ → E →ᵃ[ℝ] ℝ}

omit [FiniteDimensional ℝ E] in
theorem IsCellClosed.iUnion {J : Type*} {C : J → Set E}
    (hC : ∀ j, IsCellClosed l (C j)) : IsCellClosed l (⋃ j, C j) := by
  intro x hx y hy
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨j, hC j x hxj hy⟩

omit [FiniteDimensional ℝ E] in
theorem isCellClosed_closedCell (l : ι → E →ᵃ[ℝ] ℝ) (σ : ι → SignType) :
    IsCellClosed l (closedCell l σ) :=
  fun _ hx => closedCell_signVec_subset l hx

omit [FiniteDimensional ℝ E] in
theorem IsCellClosed.refine {P : Set E} (hP : IsCellClosed l P)
    (r : ι → κ) (hr : ∀ i, m (r i) = l i) : IsCellClosed m P := by
  intro x hx y hy
  apply hP x hx
  intro i
  simpa only [signVec, hr] using hy (r i)

omit [FiniteDimensional ℝ E] in
theorem isCellClosed_setOf_nonpos (l : ι → E →ᵃ[ℝ] ℝ) (i : ι) :
    IsCellClosed l {x | l i x ≤ 0} := by
  intro x hx y hy
  have hyi := (mem_closedCell_iff_forall l).mp hy i
  change l i x ≤ 0 at hx
  rcases hx.lt_or_eq with hx | hx
  · exact hyi.2.2 (sign_eq_neg_one_iff.mpr hx)
  · exact (hyi.1 (sign_eq_zero_iff.mpr hx)).le

omit [FiniteDimensional ℝ E] in
theorem IsCellClosed.iInter {J : Type*} {C : J → Set E}
    (hC : ∀ j, IsCellClosed l (C j)) : IsCellClosed l (⋂ j, C j) := by
  intro x hx y hy
  exact mem_iInter.mpr fun j => hC j x (mem_iInter.mp hx j) hy

omit [FiniteDimensional ℝ E] in
theorem exists_isCellClosed_of_forall_isPolyhedron {J : Type*} [Finite J]
    (C : J → Set E) (hC : ∀ j, IsPolyhedron (C j)) :
    ∃ (ι : Type) (_ : Finite ι) (l : ι → E →ᵃ[ℝ] ℝ), ∀ j, IsCellClosed l (C j) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  choose κ hκ D hD hCD using fun j : Fin n => hC (e.symm j)
  let _ : ∀ j, Finite (κ j) := hκ
  choose η hη L c hD' using fun p : (Σ j, κ j) => (hD p.1 p.2).2
  let _ : ∀ p, Finite (η p) := hη
  let l : (Σ p, η p) → E →ᵃ[ℝ] ℝ := fun q =>
    (L q.1 q.2).toAffineMap - AffineMap.const ℝ E (c q.1 q.2)
  have hcell : ∀ p : (Σ j, κ j), IsCellClosed l (D p.1 p.2) := by
    intro p
    have heq : D p.1 p.2 = ⋂ k, {x | l ⟨p, k⟩ x ≤ 0} := by
      ext x
      rw [hD' p]
      simp only [mem_ofPred_eq, mem_iInter]
      change (∀ k, L p k x ≤ c p k) ↔ ∀ k, L p k x - c p k ≤ 0
      simp only [sub_nonpos]
    rw [heq]
    exact IsCellClosed.iInter fun k => isCellClosed_setOf_nonpos l ⟨p, k⟩
  refine ⟨Σ p, η p, inferInstance, l, fun j => ?_⟩
  have heq := hCD (e j)
  rw [e.symm_apply_apply] at heq
  rw [heq]
  exact IsCellClosed.iUnion fun i => hcell ⟨e j, i⟩

theorem isPolyhedron_closedCell_of_mem_cellsOf [Finite ι] {P : Set E}
    (hP : IsCellClosed l P) (hPc : IsCompact P) {σ : ι → SignType}
    (hσ : σ ∈ cellsOf l P) : IsPolyhedron (closedCell l σ) := by
  classical
  let K := cellDerived l (closedCell l σ)
  let _ : Finite K.faces := (finite_cellDerived_faces l _).to_subtype
  have hspace : K.space = closedCell l σ :=
    space_cellDerived l _ (isCellClosed_closedCell l σ)
      (isCompact_closedCell_of_mem_cellsOf l P hP hPc hσ)
  rw [← hspace]
  exact isPolyhedron_space K

end Arrangements

section AffineLifts

variable {ι κ : Type*} (l : ι → E →ᵃ[ℝ] ℝ) (m : κ → F →ᵃ[ℝ] ℝ)
  (A : E →ᵃ[ℝ] F)

omit [FiniteDimensional ℝ E] in
theorem openCell_subset_image_openCell_of_isCellClosed [Finite κ]
    {σ : ι → SignType} {τ : κ → SignType}
    (himage : IsCellClosed m (A '' closedCell l σ))
    {p : E} (hp : p ∈ openCell l σ) (hAp : A p ∈ openCell m τ) :
    openCell m τ ⊆ A '' openCell l σ := by
  intro y hy
  have hcell : closedCell m τ ⊆ A '' closedCell l σ := by
    have h := himage (A p) ⟨p, openCell_subset_closedCell l σ hp, rfl⟩
    rwa [show signVec m (A p) = τ from hAp] at h
  obtain ⟨δ, hδ, hext⟩ := exists_extension_of_mem_openCell m
    (openCell_subset_closedCell m τ hAp) hy
  obtain ⟨z, hz, hAz⟩ := hcell
    (openCell_subset_closedCell m τ (hext δ ⟨hδ.le, le_rfl⟩))
  have hden : 0 < 1 + δ := by positivity
  have hsum : δ / (1 + δ) + 1 / (1 + δ) = 1 := by
    rw [← add_div, add_comm δ, div_self hden.ne']
  refine ⟨(δ / (1 + δ)) • p + (1 / (1 + δ)) • z,
    combo_mem_openCell l hp hz (div_pos hδ hden) (by positivity) hsum, ?_⟩
  rw [Convex.combo_affine_apply hsum, hAz, smul_add, smul_smul, smul_sub]
  have hcoeff : 1 / (1 + δ) * δ = δ / (1 + δ) := by ring
  rw [hcoeff]
  have hsum' : 1 / (1 + δ) + δ / (1 + δ) = 1 := by linarith
  calc
    _ = (1 / (1 + δ)) • y + (δ / (1 + δ)) • y := by abel
    _ = y := by rw [← add_smul, hsum', one_smul]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
def pullbackArrangement : ι ⊕ κ → E →ᵃ[ℝ] ℝ :=
  Sum.elim l fun k => (m k).comp A

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem mem_openCell_pullbackArrangement {σ : ι ⊕ κ → SignType} {x : E} :
    x ∈ openCell (pullbackArrangement l m A) σ ↔
      x ∈ openCell l (σ ∘ Sum.inl) ∧ A x ∈ openCell m (σ ∘ Sum.inr) := by
  constructor
  · intro hx
    exact ⟨funext fun i => congrFun hx (Sum.inl i),
      funext fun k => congrFun hx (Sum.inr k)⟩
  · rintro ⟨hx, hAx⟩
    funext i
    rcases i with i | k
    · exact congrFun hx i
    · exact congrFun hAx k

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem IsCellClosed.pullbackArrangement {P : Set E} (hP : IsCellClosed l P) :
    IsCellClosed (pullbackArrangement l m A) P :=
  hP.refine Sum.inl fun _ => rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem mem_cellsOf_of_mem_cellsOf_pullbackArrangement {P : Set E} {Q : Set F}
    (hA : MapsTo A P Q) {σ : ι ⊕ κ → SignType}
    (hσ : σ ∈ cellsOf (pullbackArrangement l m A) P) :
    σ ∘ Sum.inr ∈ cellsOf m Q := by
  obtain ⟨x, hx, hs⟩ := hσ
  exact ⟨A x, hA hx, funext fun k => congrFun hs (Sum.inr k)⟩

omit [FiniteDimensional ℝ E] in
theorem exists_cellCenters_pullbackArrangement [Finite κ] {P : Set E} {Q : Set F}
    (hP : IsCellClosed l P) (hA : MapsTo A P Q)
    (himage : ∀ σ ∈ cellsOf l P, IsCellClosed m (A '' closedCell l σ))
    (c : CellCenters m Q) :
    ∃ d : CellCenters (pullbackArrangement l m A) P,
      ∀ σ ∈ cellsOf (pullbackArrangement l m A) P,
        A (d.point σ) = c.point (σ ∘ Sum.inr) := by
  classical
  have hex (σ : ι ⊕ κ → SignType)
      (hσ : σ ∈ cellsOf (pullbackArrangement l m A) P) :
      ∃ x, (x ∈ P ∧ x ∈ openCell (pullbackArrangement l m A) σ) ∧
        A x = c.point (σ ∘ Sum.inr) := by
    obtain ⟨p, hp, hs⟩ := hσ
    have hp' := (mem_openCell_pullbackArrangement l m A).mp hs
    have hσl : σ ∘ Sum.inl ∈ cellsOf l P := ⟨p, hp, hp'.1⟩
    have hσr : σ ∘ Sum.inr ∈ cellsOf m Q := ⟨A p, hA hp, hp'.2⟩
    obtain ⟨x, hx, hAx⟩ := openCell_subset_image_openCell_of_isCellClosed l m A
      (himage _ hσl) hp'.1 hp'.2 (c.mem_openCell hσr)
    refine ⟨x, ⟨?_, (mem_openCell_pullbackArrangement l m A).mpr ⟨hx, ?_⟩⟩, hAx⟩
    · exact closedCell_subset_of_isCellClosed l P hP hσl
        (openCell_subset_closedCell l _ hx)
    · rw [hAx]
      exact c.mem_openCell hσr
  let p (σ : ι ⊕ κ → SignType) :=
    if hσ : σ ∈ cellsOf (pullbackArrangement l m A) P then (hex σ hσ).choose else 0
  have hp (σ : ι ⊕ κ → SignType) (hσ : σ ∈ cellsOf (pullbackArrangement l m A) P) :
      (p σ ∈ P ∧ p σ ∈ openCell (pullbackArrangement l m A) σ) ∧
        A (p σ) = c.point (σ ∘ Sum.inr) := by
    dsimp only [p]
    rw [dite_eq_left hσ]
    exact (hex σ hσ).choose_spec
  exact ⟨⟨p, fun σ hσ => (hp σ hσ).1⟩, fun σ hσ => (hp σ hσ).2⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
open Classical in
theorem image_mem_derived_faces_of_centers_map [Finite ι] [Finite κ]
    [DecidableEq E] [DecidableEq F]
    {P : Set E} {Q : Set F} (hA : MapsTo A P Q)
    (d : CellCenters (pullbackArrangement l m A) P) (c : CellCenters m Q)
    (hc : ∀ σ ∈ cellsOf (pullbackArrangement l m A) P,
      A (d.point σ) = c.point (σ ∘ Sum.inr))
    {s : Finset E} (hs : s ∈ (d.derived (pullbackArrangement l m A) P).faces) :
    s.image A ∈ (c.derived m Q).faces := by
  obtain ⟨e, he, hne, rfl⟩ := (CellCenters.mem_derived_faces_iff _ _ _).mp hs
  let r : (ι ⊕ κ → SignType) → (κ → SignType) := fun σ => σ ∘ Sum.inr
  have hflag : IsCellFlag m Q (e.image r) := by
    constructor
    · intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      exact mem_cellsOf_of_mem_cellsOf_pullbackArrangement l m A hA (he.mem_cells hσ)
    · intro τ hτ τ' hτ'
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      obtain ⟨σ', hσ', rfl⟩ := Finset.mem_image.mp hτ'
      rcases he.le_or_le hσ hσ' with h | h
      · exact Or.inl fun k => h (Sum.inr k)
      · exact Or.inr fun k => h (Sum.inr k)
  rw [CellCenters.mem_derived_faces_iff]
  refine ⟨e.image r, hflag, hne.image r, ?_⟩
  rw [Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun σ hσ => hc σ (he.mem_cells hσ)
end AffineLifts
open Classical in
theorem exists_isSubdivision_affineMap [DecidableEq F]
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (A : E →ᵃ[ℝ] F) (hA : MapsTo A K.space L.space) :
    ∃ (K' : Geometry.SimplicialComplex ℝ E) (L' : Geometry.SimplicialComplex ℝ F),
      K'.faces.Finite ∧ L'.faces.Finite ∧ IsSubdivision K' K ∧ IsSubdivision L' L ∧
      (∀ s ∈ K'.faces, s.image A ∈ L'.faces) ∧ EqOn (simplicialMap K' A) A K.space := by
  obtain ⟨ι, hι, l, hl⟩ := exists_isCellClosed_of_forall_isPolyhedron
    (fun s : K.faces => convexHull ℝ ((s : Finset E) : Set E))
    (fun s => isPolyhedron_convexHull_of_affineIndependent _ (K.indep s.2))
  let _ := hι
  have hP : IsCellClosed l K.space := by
    intro x hx y hy
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    exact K.convexHull_subset_space hs (hl ⟨s, hs⟩ x hxs hy)
  let C : cellsOf l K.space ⊕ L.faces → Set F :=
    Sum.elim (fun σ => A '' closedCell l σ) fun t => convexHull ℝ ((t : Finset F) : Set F)
  have hC : ∀ i, IsPolyhedron (C i) := by
    rintro (σ | t)
    · exact (isPolyhedron_closedCell_of_mem_cellsOf hP
        (isPolyhedron_space K).isCompact σ.2).image_affineMap A
    · exact isPolyhedron_convexHull_of_affineIndependent _ (L.indep t.2)
  obtain ⟨κ, hκ, m, hm⟩ := exists_isCellClosed_of_forall_isPolyhedron C hC
  let _ := hκ
  have hQ : IsCellClosed m L.space := by
    intro x hx y hy
    obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hx
    exact L.convexHull_subset_space ht (hm (Sum.inr ⟨t, ht⟩) x hxt hy)
  let c := canonicalCellCenters m L.space
  obtain ⟨d, hd⟩ := exists_cellCenters_pullbackArrangement l m A hP hA
    (fun σ hσ => hm (Sum.inl ⟨σ, hσ⟩)) c
  let K' := d.derived (pullbackArrangement l m A) K.space
  let L' := c.derived m L.space
  have hK' : K'.space = K.space :=
    d.space_derived _ _ (hP.pullbackArrangement l m A) (isPolyhedron_space K).isCompact
  have hL' : L'.space = L.space :=
    c.space_derived _ _ hQ (isPolyhedron_space L).isCompact
  have hsub : IsSubdivision K' K :=
    isSubdivision_of_forall_convexHull_eq_biUnion K' K hK' fun s hs =>
      d.eq_biUnion_derived_faces _ _ (hP.pullbackArrangement l m A)
        (isPolyhedron_space K).isCompact ((hl ⟨s, hs⟩).pullbackArrangement l m A)
        (K.convexHull_subset_space hs)
  have hsub' : IsSubdivision L' L :=
    isSubdivision_of_forall_convexHull_eq_biUnion L' L hL' fun t ht =>
      c.eq_biUnion_derived_faces _ _ hQ (isPolyhedron_space L).isCompact
        (hm (Sum.inr ⟨t, ht⟩)) (L.convexHull_subset_space ht)
  refine ⟨K', L', d.finite_derived_faces _ _, c.finite_derived_faces _ _, hsub, hsub',
    fun s hs => image_mem_derived_faces_of_centers_map l m A hA d c hd hs, ?_⟩
  rw [← hK']
  exact simplicialMap_eq_of_forall_affineOn K' A fun _ _ => ⟨A, fun _ _ => rfl⟩
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
open Classical in
theorem image_convexHull_of_eqOn_affineMap [DecidableEq F] {f : E → F}
    (s : Finset E) (A : E →ᵃ[ℝ] F)
    (hA : EqOn f A (convexHull ℝ (s : Set E))) :
    f '' convexHull ℝ (s : Set E) = convexHull ℝ (↑(s.image f) : Set F) := by
  rw [hA.image_eq, A.image_convexHull, Finset.coe_image]
  exact congrArg (convexHull ℝ) (hA.mono (subset_convexHull ℝ _)).image_eq.symm

open Classical in
theorem IsPiecewiseAffineOn.exists_isSubdivision_simplicialMap [DecidableEq F]
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] {f : E → F}
    (hf : IsPiecewiseAffineOn f K.space) (hmap : MapsTo f K.space L.space) :
    ∃ (K' : Geometry.SimplicialComplex ℝ E) (L' : Geometry.SimplicialComplex ℝ F),
      K'.faces.Finite ∧ L'.faces.Finite ∧ IsSubdivision K' K ∧ IsSubdivision L' L ∧
      (∀ s ∈ K'.faces, s.image f ∈ L'.faces) ∧ EqOn (simplicialMap K' f) f K.space := by
  obtain ⟨K₀, hK₀, hfin₀, hAff⟩ := hf.exists_isSubdivision_affineOn_faces K
  let _ : Finite K₀.faces := hfin₀.to_subtype
  let g : E → E × F := fun x => (x, f x)
  have hgraph : ∀ s ∈ K₀.faces, ∃ B : E →ᵃ[ℝ] E × F,
      EqOn g B (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, hA⟩ := hAff s hs
    exact ⟨(AffineMap.id ℝ E).prod A, fun x hx => Prod.ext rfl (hA hx)⟩
  have hginj : InjOn g K₀.space := fun _ _ _ _ h => congrArg Prod.fst h
  obtain ⟨G, hGfin, hGspace, hGfaces, -⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces K₀ hgraph hginj
  let _ : Finite G.faces := hGfin.to_subtype
  let p : E × F →ᵃ[ℝ] E := (LinearMap.fst ℝ E F).toAffineMap
  let q : E × F →ᵃ[ℝ] F := (LinearMap.snd ℝ E F).toAffineMap
  have hq : MapsTo q G.space L.space := by
    intro z hz
    rw [hGspace] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hmap (hK₀.space_eq ▸ hx)
  have hfg : ∀ z ∈ G.space, f (p z) = q z := by
    intro z hz
    rw [hGspace] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rfl
  obtain ⟨G', L', hG'fin, hL'fin, hG', hL', hfaces, -⟩ :=
    exists_isSubdivision_affineMap G L q hq
  let _ : Finite G'.faces := hG'fin.to_subtype
  have hp : InjOn p G'.space := by
    intro z hz w hw hzw
    apply Prod.ext hzw
    change q z = q w
    rw [← hfg z (hG'.space_eq ▸ hz), ← hfg w (hG'.space_eq ▸ hw), hzw]
  obtain ⟨K', hK'fin, hK'space, hK'faces, -⟩ :=
    exists_simplicialComplex_image_of_affineOn_faces G'
      (fun _ _ => ⟨p, fun _ _ => rfl⟩) hp
  have hspace₀ : K'.space = K₀.space := by
    rw [hK'space, hG'.space_eq, hGspace, image_image]
    exact image_id _
  have hsub : IsSubdivision K' K₀ := by
    refine ⟨hspace₀, fun s hs => ?_⟩
    obtain ⟨u, hu, rfl⟩ := (hK'faces s).mp hs
    obtain ⟨v, hv, huv⟩ := hG'.exists_face_subset hu
    obtain ⟨t, ht, rfl⟩ := (hGfaces v).mp hv
    refine ⟨t, ht, ?_⟩
    rw [Finset.coe_image, ← p.image_convexHull]
    rintro x ⟨z, hz, rfl⟩
    have hzt := huv hz
    obtain ⟨B, hB⟩ := hgraph t ht
    rw [← image_convexHull_of_eqOn_affineMap t B hB] at hzt
    obtain ⟨y, hy, rfl⟩ := hzt
    exact hy
  have hAff' : ∀ s ∈ K'.faces, ∃ A : E →ᵃ[ℝ] F,
      EqOn f A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hsub.exists_face_subset hs
    obtain ⟨A, hA⟩ := hAff t ht
    exact ⟨A, hA.mono hst⟩
  refine ⟨K', L', hK'fin, hL'fin, hsub.trans hK₀, hL', ?_, ?_⟩
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := (hK'faces s).mp hs
    have heq : (u.image p).image f = u.image q := by
      rw [Finset.image_image]
      exact Finset.image_congr fun z hz =>
        hfg z (hG'.space_eq ▸ G'.convexHull_subset_space hu (subset_convexHull ℝ _ hz))
    rw [heq]
    exact hfaces u hu
  · rw [← hK₀.space_eq, ← hspace₀]
    exact simplicialMap_eq_of_forall_affineOn K' f hAff'
end DifferentialGeometry.Topology.PiecewiseLinear
