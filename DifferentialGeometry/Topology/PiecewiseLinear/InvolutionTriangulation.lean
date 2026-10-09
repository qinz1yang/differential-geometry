/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem _root_.Convex.disjoint_image_affineInvolution
    {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} (hC : Convex ℝ C)
    (A : E →ᵃ[ℝ] E) (hA : Function.Involutive A)
    (hfree : ∀ x ∈ C, A x ≠ x) : Disjoint C (A '' C) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨y, hy, rfl⟩
  have hmid : (1 / 2 : ℝ) • A y + (1 / 2 : ℝ) • y ∈ C :=
    hC hz hy (by norm_num) (by norm_num) (by norm_num)
  apply hfree _ hmid
  rw [Convex.combo_affine_apply (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1), hA]
  exact add_comm _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPolyhedron.exists_simplicialComplex_affineInvolution_relative
    {P : Set E} (hP : IsPolyhedron P) (A : E →ᵃ[ℝ] E)
    (hA : Function.Involutive A) (hAP : MapsTo A P P)
    {J : Type*} [Finite J] (C : J → Set E) (hC : ∀ j, IsPolyhedron (C j))
    (hCP : ∀ j, C j ⊆ P) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      (∀ s ∈ K.faces, s.image A ∈ K.faces) ∧
      ∀ j, (restrict K (C j)).space = C j := by
  let Q : Option J → Set E := fun j => j.elim P C
  have hQ : ∀ j, IsPolyhedron (Q j) := by
    rintro (_ | j)
    · exact hP
    · exact hC j
  obtain ⟨ι, hι, l, hl⟩ := exists_isCellClosed_of_forall_isPolyhedron Q hQ
  let _ := hι
  let m : ι ⊕ ι → E →ᵃ[ℝ] ℝ := Sum.elim l (fun i => (l i).comp A)
  let r : (ι ⊕ ι → SignType) → (ι ⊕ ι → SignType) := fun σ => σ ∘ Sum.swap
  have hrr (σ : ι ⊕ ι → SignType) : r (r σ) = σ := by
    funext i
    cases i <;> rfl
  have hm (i : ι ⊕ ι) (x : E) : m i (A x) = m (Sum.swap i) x := by
    cases i with
    | inl i => rfl
    | inr i => exact congrArg (l i) (hA x)
  have hsign (x : E) : signVec m (A x) = r (signVec m x) := by
    funext i
    exact congrArg SignType.sign (hm i x)
  have hopen {x : E} {σ : ι ⊕ ι → SignType} (hx : x ∈ openCell m σ) :
      A x ∈ openCell m (r σ) := by
    change signVec m (A x) = r σ
    rw [hsign, hx]
  have hcell {σ : ι ⊕ ι → SignType} (hσ : σ ∈ cellsOf m P) :
      r σ ∈ cellsOf m P := by
    obtain ⟨x, hx, rfl⟩ := hσ
    exact ⟨A x, hAP hx, hsign x⟩
  have hPm : IsCellClosed m P := (hl none).refine Sum.inl fun _ => rfl
  have hCm (j : J) : IsCellClosed m (C j) :=
    (hl (some j)).refine Sum.inl fun _ => rfl
  let p (σ : ι ⊕ ι → SignType) : E :=
    (1 / 2 : ℝ) • cellPt m P σ + (1 / 2 : ℝ) • A (cellPt m P (r σ))
  have hp (σ : ι ⊕ ι → SignType) (hσ : σ ∈ cellsOf m P) :
      p σ ∈ P ∧ p σ ∈ openCell m σ := by
    have hfirst := (cellPt_spec m P hσ).2
    have hsecond : A (cellPt m P (r σ)) ∈ openCell m σ := by
      simpa only [hrr] using hopen (cellPt_spec m P (hcell hσ)).2
    have hpoint : p σ ∈ openCell m σ :=
      combo_mem_openCell m hfirst (openCell_subset_closedCell m σ hsecond)
        (by norm_num) (by norm_num) (by norm_num)
    exact ⟨closedCell_subset_of_isCellClosed m P hPm hσ
      (openCell_subset_closedCell m σ hpoint), hpoint⟩
  have hAp (σ : ι ⊕ ι → SignType) : A (p σ) = p (r σ) := by
    dsimp only [p]
    rw [Convex.combo_affine_apply (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1), hA, hrr]
    exact add_comm _ _
  let c : CellCenters m P := ⟨p, hp⟩
  let K := c.derived m P
  have hfaces {s : Finset E} (hs : s ∈ K.faces) : s.image A ∈ K.faces := by
    obtain ⟨d, hd, hne, rfl⟩ := (CellCenters.mem_derived_faces_iff m P c).mp hs
    have hflag : IsCellFlag m P (d.image r) := by
      constructor
      · intro τ hτ
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
        exact hcell (hd.mem_cells hσ)
      · intro τ hτ τ' hτ'
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
        obtain ⟨σ', hσ', rfl⟩ := Finset.mem_image.mp hτ'
        rcases hd.le_or_le hσ hσ' with h | h
        · exact Or.inl fun i => h (Sum.swap i)
        · exact Or.inr fun i => h (Sum.swap i)
    rw [CellCenters.mem_derived_faces_iff]
    refine ⟨d.image r, hflag, hne.image r, ?_⟩
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr fun σ _ => hAp σ
  refine ⟨K, c.finite_derived_faces m P, c.space_derived m P hPm hP.isCompact,
    fun _ hs => hfaces hs, fun j => ?_⟩
  exact restrict_space_of_eq_biUnion K (C j)
    (c.eq_biUnion_derived_faces m P hPm hP.isCompact (hCm j) (hCP j))

open Classical in
theorem IsPolyhedron.exists_simplicialComplex_affineInvolution
    {P : Set E} (hP : IsPolyhedron P) (A : E →ᵃ[ℝ] E)
    (hA : Function.Involutive A) (hAP : MapsTo A P P) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∀ s ∈ K.faces, s.image A ∈ K.faces := by
  obtain ⟨K, hfin, hspace, hfaces, -⟩ :=
    hP.exists_simplicialComplex_affineInvolution_relative A hA hAP
      (fun j : Empty => j.elim) (fun j => j.elim) (fun j => j.elim)
  exact ⟨K, hfin, hspace, hfaces⟩

end DifferentialGeometry.Topology.PiecewiseLinear
