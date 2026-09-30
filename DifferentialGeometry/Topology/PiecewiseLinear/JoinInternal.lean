/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Join
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section InternalJoin

variable [DecidableEq E] (K A B : Geometry.SimplicialComplex ℝ E)

def internalJoinFaces : Set (Finset E) :=
  {u | ∃ s t : Finset E, (s = ∅ ∨ s ∈ A.faces) ∧ (t = ∅ ∨ t ∈ B.faces) ∧
    (s.Nonempty ∨ t.Nonempty) ∧ u = s ∪ t}

theorem mem_internalJoinFaces_iff {u : Finset E} :
    u ∈ internalJoinFaces A B ↔ ∃ s t : Finset E, (s = ∅ ∨ s ∈ A.faces) ∧
      (t = ∅ ∨ t ∈ B.faces) ∧ (s.Nonempty ∨ t.Nonempty) ∧ u = s ∪ t := Iff.rfl

theorem internalJoinFaces_isRelLowerSet :
    IsRelLowerSet (internalJoinFaces A B) Finset.Nonempty := by
  rintro u ⟨s, t, hs, ht, hne, rfl⟩
  refine ⟨?_, fun w hwu hw => ?_⟩
  · rcases hne with h | h
    · exact h.mono Finset.subset_union_left
    · exact h.mono Finset.subset_union_right
  · refine ⟨w ∩ s, w ∩ t, ?_, ?_, ?_, ?_⟩
    · rcases hs with rfl | hs
      · exact Or.inl (Finset.inter_empty w)
      · rcases (w ∩ s).eq_empty_or_nonempty with h | h
        · exact Or.inl h
        · exact Or.inr (A.down_closed hs Finset.inter_subset_right h)
    · rcases ht with rfl | ht
      · exact Or.inl (Finset.inter_empty w)
      · rcases (w ∩ t).eq_empty_or_nonempty with h | h
        · exact Or.inl h
        · exact Or.inr (B.down_closed ht Finset.inter_subset_right h)
    · obtain ⟨x, hx⟩ := hw
      rcases Finset.mem_union.mp (hwu hx) with h | h
      · exact Or.inl ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩
      · exact Or.inr ⟨x, Finset.mem_inter.mpr ⟨hx, h⟩⟩
    · rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hwu]

variable (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces)
  (hunion : ∀ s ∈ A.faces, ∀ t ∈ B.faces, s ∪ t ∈ K.faces)

include hA hB hunion in
theorem internalJoinFaces_subset : internalJoinFaces A B ⊆ K.faces := by
  rintro u ⟨s, t, hs, ht, hne, rfl⟩
  rcases hs with rfl | hs
  · rcases ht with rfl | ht
    · exact absurd (hne.elim id id) Finset.not_nonempty_empty
    · rw [Finset.empty_union]
      exact hB ht
  · rcases ht with rfl | ht
    · rw [Finset.union_empty]
      exact hA hs
    · exact hunion s hs t ht

def internalJoin : Geometry.SimplicialComplex ℝ E where
  faces := internalJoinFaces A B
  isRelLowerSet_faces := internalJoinFaces_isRelLowerSet A B
  indep hs := K.indep (internalJoinFaces_subset K A B hA hB hunion hs)
  inter_subset_convexHull hs ht :=
    K.inter_subset_convexHull (internalJoinFaces_subset K A B hA hB hunion hs)
      (internalJoinFaces_subset K A B hA hB hunion ht)

theorem mem_internalJoin_faces_iff {u : Finset E} :
    u ∈ (internalJoin K A B hA hB hunion).faces ↔ ∃ s t : Finset E, (s = ∅ ∨ s ∈ A.faces) ∧
      (t = ∅ ∨ t ∈ B.faces) ∧ (s.Nonempty ∨ t.Nonempty) ∧ u = s ∪ t := Iff.rfl

theorem internalJoin_faces_subset : (internalJoin K A B hA hB hunion).faces ⊆ K.faces :=
  internalJoinFaces_subset K A B hA hB hunion

theorem internalJoin_space_subset : (internalJoin K A B hA hB hunion).space ⊆ K.space :=
  space_mono_of_faces_subset (internalJoin_faces_subset K A B hA hB hunion)

theorem internalJoin_faces_finite [Finite A.faces] [Finite B.faces] :
    (internalJoin K A B hA hB hunion).faces.Finite := by
  refine ((((Set.toFinite A.faces).insert ∅).prod ((Set.toFinite B.faces).insert ∅)).image
    fun p : Finset E × Finset E => p.1 ∪ p.2).subset ?_
  rintro u ⟨s, t, hs, ht, -, rfl⟩
  refine ⟨(s, t), ⟨?_, ?_⟩, rfl⟩
  · rcases hs with rfl | h
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ h
  · rcases ht with rfl | h
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ h

theorem union_mem_internalJoin {s t : Finset E} (hs : s = ∅ ∨ s ∈ A.faces)
    (ht : t = ∅ ∨ t ∈ B.faces) (hne : s.Nonempty ∨ t.Nonempty) :
    s ∪ t ∈ (internalJoin K A B hA hB hunion).faces := ⟨s, t, hs, ht, hne, rfl⟩

end InternalJoin

section VertexMap

variable (A : Geometry.SimplicialComplex ℝ E)

open Classical in
noncomputable def internalJoinVertex (v : E) : E × E × ℝ :=
  if {v} ∈ A.faces then joinFst E E v else joinSnd E E v

noncomputable def internalJoinVertexInv (z : E × E × ℝ) : E :=
  if glueHeight E E z = 0 then glueFst E E z else glueSnd E E z

theorem internalJoinVertex_of_mem {v : E} (hv : {v} ∈ A.faces) :
    internalJoinVertex A v = joinFst E E v := by
  rw [internalJoinVertex, ite_eq_left hv]

theorem internalJoinVertex_of_notMem {v : E} (hv : {v} ∉ A.faces) :
    internalJoinVertex A v = joinSnd E E v := by
  rw [internalJoinVertex, ite_eq_right hv]

theorem internalJoinVertexInv_joinFst (v : E) : internalJoinVertexInv (joinFst E E v) = v := by
  rw [internalJoinVertexInv, ite_eq_left (glueHeight_joinFst (F := E) v), glueFst_joinFst]

theorem internalJoinVertexInv_joinSnd (w : E) : internalJoinVertexInv (joinSnd E E w) = w := by
  have h : ¬glueHeight E E (joinSnd E E w) = 0 := by
    rw [glueHeight_joinSnd]
    exact one_ne_zero
  rw [internalJoinVertexInv, ite_eq_right h, glueSnd_joinSnd]

theorem internalJoinVertexInv_comp_joinFst :
    internalJoinVertexInv ∘ joinFst E E = (id : E → E) :=
  funext internalJoinVertexInv_joinFst

theorem internalJoinVertexInv_comp_joinSnd :
    internalJoinVertexInv ∘ joinSnd E E = (id : E → E) :=
  funext internalJoinVertexInv_joinSnd

end VertexMap

section GlueIso

theorem singleton_notMem_of_mem_faces (A B : Geometry.SimplicialComplex ℝ E)
    (hdisj : ∀ s ∈ A.faces, ∀ t ∈ B.faces, Disjoint s t)
    {t : Finset E} (ht : t ∈ B.faces) {w : E} (hw : w ∈ t) : {w} ∉ A.faces := fun hmem =>
  Finset.disjoint_left.mp (hdisj _ hmem _ ht) (Finset.mem_singleton_self w) hw

theorem isGlueIso_internalJoin [DecidableEq E] (K A B : Geometry.SimplicialComplex ℝ E)
    (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces)
    (hunion : ∀ s ∈ A.faces, ∀ t ∈ B.faces, s ∪ t ∈ K.faces)
    (hdisj : ∀ s ∈ A.faces, ∀ t ∈ B.faces, Disjoint s t) :
    IsGlueIso (internalJoin K A B hA hB hunion) (joinComplex A B) (internalJoinVertex A)
      internalJoinVertexInv where
  image₁ := by
    rintro u ⟨s, t, hs, ht, hne, rfl⟩
    have hsimg : s.image (internalJoinVertex A) = s.image (joinFst E E) := by
      refine Finset.image_congr fun v hv => ?_
      have hvs : v ∈ s := Finset.mem_coe.mp hv
      rcases hs with rfl | hs'
      · exact absurd hvs (Finset.notMem_empty v)
      · exact internalJoinVertex_of_mem A
          (A.down_closed hs' (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v))
    have htimg : t.image (internalJoinVertex A) = t.image (joinSnd E E) := by
      refine Finset.image_congr fun w hw => ?_
      have hwt : w ∈ t := Finset.mem_coe.mp hw
      rcases ht with rfl | ht'
      · exact absurd hwt (Finset.notMem_empty w)
      · exact internalJoinVertex_of_notMem A
          (singleton_notMem_of_mem_faces A B hdisj ht' hwt)
    rw [Finset.image_union, hsimg, htimg]
    exact union_image_mem_joinComplex A B hs ht hne
  image₂ := by
    rintro z ⟨σ, τ, hσ, hτ, hne, rfl⟩
    rw [Finset.image_union, Finset.image_image, Finset.image_image,
      internalJoinVertexInv_comp_joinFst, internalJoinVertexInv_comp_joinSnd, Finset.image_id,
      Finset.image_id]
    exact ⟨σ, τ, hσ, hτ, hne, rfl⟩
  left := by
    rintro u ⟨s, t, hs, ht, -, rfl⟩ v hv
    rcases Finset.mem_union.mp hv with h | h
    · rcases hs with rfl | hs'
      · exact absurd h (Finset.notMem_empty v)
      · rw [internalJoinVertex_of_mem A
          (A.down_closed hs' (Finset.singleton_subset_iff.mpr h) (Finset.singleton_nonempty v)),
          internalJoinVertexInv_joinFst]
    · rcases ht with rfl | ht'
      · exact absurd h (Finset.notMem_empty v)
      · rw [internalJoinVertex_of_notMem A (singleton_notMem_of_mem_faces A B hdisj ht' h),
          internalJoinVertexInv_joinSnd]
  right := by
    rintro z ⟨σ, τ, hσ, hτ, -, rfl⟩ y hy
    rcases Finset.mem_union.mp hy with h | h
    · obtain ⟨v, hvσ, rfl⟩ := Finset.mem_image.mp h
      rcases hσ with rfl | hσ'
      · exact absurd hvσ (Finset.notMem_empty v)
      · rw [internalJoinVertexInv_joinFst, internalJoinVertex_of_mem A
          (A.down_closed hσ' (Finset.singleton_subset_iff.mpr hvσ) (Finset.singleton_nonempty v))]
    · obtain ⟨w, hwτ, rfl⟩ := Finset.mem_image.mp h
      rcases hτ with rfl | hτ'
      · exact absurd hwτ (Finset.notMem_empty w)
      · rw [internalJoinVertexInv_joinSnd,
          internalJoinVertex_of_notMem A (singleton_notMem_of_mem_faces A B hdisj hτ' hwτ)]

end GlueIso

section SimplexInstances

theorem disjoint_of_subset_sdiff {α : Type*} [DecidableEq α] {T S s t : Finset α} (hs : s ⊆ S)
    (ht : t ⊆ T \ S) : Disjoint s t :=
  Finset.disjoint_of_subset_left hs (Finset.disjoint_of_subset_right ht Finset.disjoint_sdiff)

theorem simplexComplex_faces_subset_of_subset {T S : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hS : AffineIndependent ℝ ((↑) : S → E))
    (hST : S ⊆ T) : (simplexComplex S hS).faces ⊆ (simplexComplex T hT).faces :=
  fun _ hs => ⟨hs.1, hs.2.trans hST⟩

theorem simplexBoundary_faces_subset_simplexComplex_of_subset {T S : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hS : AffineIndependent ℝ ((↑) : S → E))
    (hST : S ⊆ T) : (simplexBoundary S hS).faces ⊆ (simplexComplex T hT).faces :=
  fun _ hs => ⟨hs.2.1, hs.1.trans hST⟩

theorem union_mem_simplexComplex_faces [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {s t : Finset E}
    (hs : s ∈ (simplexComplex T hT).faces) (ht : t ∈ (simplexComplex T hT).faces) :
    s ∪ t ∈ (simplexComplex T hT).faces :=
  ⟨hs.1.mono Finset.subset_union_left, Finset.union_subset hs.2 ht.2⟩

theorem union_mem_simplexComplex_of_faces_subset [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {A B : Geometry.SimplicialComplex ℝ E}
    (hA : A.faces ⊆ (simplexComplex T hT).faces) (hB : B.faces ⊆ (simplexComplex T hT).faces) :
    ∀ s ∈ A.faces, ∀ t ∈ B.faces, s ∪ t ∈ (simplexComplex T hT).faces :=
  fun _ hs _ ht => union_mem_simplexComplex_faces hT (hA hs) (hB ht)

theorem disjoint_faces_simplexBoundary_pair [DecidableEq E] {T σ₀ : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hσ₀T : σ₀ ⊆ T) :
    ∀ s ∈ (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T)).faces,
      ∀ t ∈ (simplexBoundary (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset)).faces,
        Disjoint s t :=
  fun _ hs _ ht => disjoint_of_subset_sdiff hs.1 ht.1

theorem disjoint_faces_simplexBoundary_simplexComplex [DecidableEq E] {T σ₀ : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hσ₀T : σ₀ ⊆ T) :
    ∀ s ∈ (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T)).faces,
      ∀ t ∈ (simplexComplex (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset)).faces,
        Disjoint s t :=
  fun _ hs _ ht => disjoint_of_subset_sdiff hs.1 ht.2

theorem simplexAvoiding_pair_eq_internalJoin [DecidableEq E] {T σ₀ : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hσ₀T : σ₀ ⊆ T) (hσ₀ne : σ₀.Nonempty)
    (hσ₀T' : σ₀ ≠ T)
    (hA : (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T)).faces ⊆
      (simplexComplex T hT).faces)
    (hB : (simplexBoundary (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset)).faces ⊆
      (simplexComplex T hT).faces)
    (hunion : ∀ s ∈ (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T)).faces,
      ∀ t ∈ (simplexBoundary (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset)).faces,
        s ∪ t ∈ (simplexComplex T hT).faces) :
    simplexAvoiding T hT {σ₀, T \ σ₀} =
      internalJoin (simplexComplex T hT)
        (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T))
        (simplexBoundary (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset))
        hA hB hunion := by
  have hTσ₀ : (T \ σ₀).Nonempty :=
    Finset.sdiff_nonempty.mpr fun h => hσ₀T' (Finset.Subset.antisymm hσ₀T h)
  ext s
  rw [mem_simplexAvoiding_faces_iff, mem_internalJoin_faces_iff]
  constructor
  · rintro ⟨hne, hsT, havoid⟩
    have h₁ : ¬σ₀ ⊆ s := havoid σ₀ (Finset.mem_insert_self _ _)
    have h₂ : ¬T \ σ₀ ⊆ s :=
      havoid (T \ σ₀) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    refine ⟨s ∩ σ₀, s ∩ (T \ σ₀), ?_, ?_, ?_, ?_⟩
    · rcases (s ∩ σ₀).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Finset.inter_subset_right, h, fun heq => h₁ ?_⟩
        rw [← heq]
        exact Finset.inter_subset_left
    · rcases (s ∩ (T \ σ₀)).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Finset.inter_subset_right, h, fun heq => h₂ ?_⟩
        rw [← heq]
        exact Finset.inter_subset_left
    · obtain ⟨v, hv⟩ := hne
      by_cases hvσ : v ∈ σ₀
      · exact Or.inl ⟨v, Finset.mem_inter.mpr ⟨hv, hvσ⟩⟩
      · exact Or.inr ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_sdiff.mpr ⟨hsT hv, hvσ⟩⟩⟩
    · rw [← Finset.inter_union_distrib_left, Finset.union_sdiff_of_subset hσ₀T,
        Finset.inter_eq_left.mpr hsT]
  · rintro ⟨a, b, ha, hb, hne, rfl⟩
    have haσ : a ⊆ σ₀ := by
      rcases ha with rfl | h
      · exact Finset.empty_subset _
      · exact h.1
    have hbσ : b ⊆ T \ σ₀ := by
      rcases hb with rfl | h
      · exact Finset.empty_subset _
      · exact h.1
    refine ⟨?_, Finset.union_subset (haσ.trans hσ₀T) (hbσ.trans Finset.sdiff_subset), ?_⟩
    · rcases hne with h | h
      · exact h.mono Finset.subset_union_left
      · exact h.mono Finset.subset_union_right
    · intro σ hσ hsub
      rw [Finset.mem_insert, Finset.mem_singleton] at hσ
      rcases hσ with h | h
      · rw [h] at hsub
        have hσa : σ₀ ⊆ a := fun v hv => by
          rcases Finset.mem_union.mp (hsub hv) with hv' | hv'
          · exact hv'
          · exact absurd hv (Finset.mem_sdiff.mp (hbσ hv')).2
        rcases ha with rfl | ha'
        · exact hσ₀ne.ne_empty (Finset.subset_empty.mp hσa)
        · exact ha'.2.2 (Finset.Subset.antisymm haσ hσa)
      · rw [h] at hsub
        have hσb : T \ σ₀ ⊆ b := fun v hv => by
          rcases Finset.mem_union.mp (hsub hv) with hv' | hv'
          · exact absurd (haσ hv') (Finset.mem_sdiff.mp hv).2
          · exact hv'
        rcases hb with rfl | hb'
        · exact hTσ₀.ne_empty (Finset.subset_empty.mp hσb)
        · exact hb'.2.2 (Finset.Subset.antisymm hbσ hσb)

theorem simplexAvoiding_singleton_eq_internalJoin [DecidableEq E] {T σ₀ : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hσ₀T : σ₀ ⊆ T) (hσ₀ne : σ₀.Nonempty)
    (hA : (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T)).faces ⊆
      (simplexComplex T hT).faces)
    (hB : (simplexComplex (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset)).faces ⊆
      (simplexComplex T hT).faces)
    (hunion : ∀ s ∈ (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T)).faces,
      ∀ t ∈ (simplexComplex (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset)).faces,
        s ∪ t ∈ (simplexComplex T hT).faces) :
    simplexAvoiding T hT {σ₀} =
      internalJoin (simplexComplex T hT)
        (simplexBoundary σ₀ (affineIndependent_of_subset hT hσ₀T))
        (simplexComplex (T \ σ₀) (affineIndependent_of_subset hT Finset.sdiff_subset))
        hA hB hunion := by
  ext s
  rw [mem_simplexAvoiding_faces_iff, mem_internalJoin_faces_iff]
  constructor
  · rintro ⟨hne, hsT, havoid⟩
    have h₁ : ¬σ₀ ⊆ s := havoid σ₀ (Finset.mem_singleton_self _)
    refine ⟨s ∩ σ₀, s ∩ (T \ σ₀), ?_, ?_, ?_, ?_⟩
    · rcases (s ∩ σ₀).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Finset.inter_subset_right, h, fun heq => h₁ ?_⟩
        rw [← heq]
        exact Finset.inter_subset_left
    · rcases (s ∩ (T \ σ₀)).eq_empty_or_nonempty with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Finset.inter_subset_right⟩
    · obtain ⟨v, hv⟩ := hne
      by_cases hvσ : v ∈ σ₀
      · exact Or.inl ⟨v, Finset.mem_inter.mpr ⟨hv, hvσ⟩⟩
      · exact Or.inr ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_sdiff.mpr ⟨hsT hv, hvσ⟩⟩⟩
    · rw [← Finset.inter_union_distrib_left, Finset.union_sdiff_of_subset hσ₀T,
        Finset.inter_eq_left.mpr hsT]
  · rintro ⟨a, b, ha, hb, hne, rfl⟩
    have haσ : a ⊆ σ₀ := by
      rcases ha with rfl | h
      · exact Finset.empty_subset _
      · exact h.1
    have hbσ : b ⊆ T \ σ₀ := by
      rcases hb with rfl | h
      · exact Finset.empty_subset _
      · exact h.2
    refine ⟨?_, Finset.union_subset (haσ.trans hσ₀T) (hbσ.trans Finset.sdiff_subset), ?_⟩
    · rcases hne with h | h
      · exact h.mono Finset.subset_union_left
      · exact h.mono Finset.subset_union_right
    · intro σ hσ hsub
      rw [Finset.mem_singleton] at hσ
      rw [hσ] at hsub
      have hσa : σ₀ ⊆ a := fun v hv => by
        rcases Finset.mem_union.mp (hsub hv) with hv' | hv'
        · exact hv'
        · exact absurd hv (Finset.mem_sdiff.mp (hbσ hv')).2
      rcases ha with rfl | ha'
      · exact hσ₀ne.ne_empty (Finset.subset_empty.mp hσa)
      · exact ha'.2.2 (Finset.Subset.antisymm haσ hσa)

end SimplexInstances

end DifferentialGeometry.Topology.PiecewiseLinear
