import DifferentialGeometry.Topology.SimplicialComplex.Realization.SimplicialGluing
import Mathlib.Data.Finset.Sum

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set _root_.Topology _root_.Geometry

noncomputable section

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
  [DecidableEq ι] [DecidableEq α] [DecidableEq β]

def commonVertexComplex (P : PreAbstractSimplicialComplex (ι ⊕ α)) :
    PreAbstractSimplicialComplex ι where
  faces := {s | s.image Sum.inl ∈ P.faces}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.image_nonempty.mp (P.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    exact (P.isRelLowerSet_faces hs).2 (Finset.image_subset_image hts)
      (Finset.image_nonempty.mpr ht)

def pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β) := Sum.map id Sum.inl

def pushoutRightVertex : ι ⊕ β → ι ⊕ (α ⊕ β) := Sum.map id Sum.inr

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] [Fintype ι] [Fintype α] [Fintype β] in
theorem pushoutLeftVertex_injective [Finite ι] [Finite α] [Finite β] : Function.Injective
    (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype α := Fintype.ofFinite α
  let : Fintype β := Fintype.ofFinite β
  rintro (i | a) (j | b) h <;> simp_all [pushoutLeftVertex]

omit [DecidableEq ι] [DecidableEq α] [DecidableEq β] [Fintype ι] [Fintype α] [Fintype β] in
theorem pushoutRightVertex_injective [Finite ι] [Finite α] [Finite β] : Function.Injective
    (pushoutRightVertex : ι ⊕ β → ι ⊕ (α ⊕ β)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype α := Fintype.ofFinite α
  let : Fintype β := Fintype.ofFinite β
  rintro (i | a) (j | b) h <;> simp_all [pushoutRightVertex]

def simplicialPushout (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    PreAbstractSimplicialComplex (ι ⊕ (α ⊕ β)) :=
  P.map pushoutLeftVertex ⊔ Q.map pushoutRightVertex

omit [Fintype ι] [Fintype α] [Fintype β] in
private theorem image_eq_common_of_pushout_image_eq [Finite ι] [Finite α] [Finite β]
    {s : Finset (ι ⊕ α)} {t : Finset (ι ⊕ β)}
    (hst : s.image (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β)) =
      t.image pushoutRightVertex) :
    s.toLeft.image Sum.inl = s ∧ t.toLeft = s.toLeft := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype α := Fintype.ofFinite α
  let : Fintype β := Fintype.ofFinite β
  have hno : ∀ a : α, Sum.inr a ∉ s := by
    intro a ha
    have h : Sum.inr (Sum.inl a) ∈ t.image pushoutRightVertex :=
      hst ▸ Finset.mem_image.mpr ⟨Sum.inr a, ha, rfl⟩
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    cases j <;> simp [pushoutRightVertex] at heq
  constructor
  · ext (i | a) <;> simp [hno]
  · ext i
    have h := Finset.ext_iff.mp hst (Sum.inl i)
    simpa [pushoutLeftVertex, pushoutRightVertex] using h.symm

omit [Fintype ι] [Fintype α] [Fintype β] in
theorem simplicialPushout_common [Finite ι] [Finite α] [Finite β] (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β))
    (hcommon : commonVertexComplex P = commonVertexComplex Q) :
    P.map (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β)) ⊓
        Q.map pushoutRightVertex = (commonVertexComplex P).map Sum.inl := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype α := Fintype.ofFinite α
  let : Fintype β := Fintype.ofFinite β
  ext u
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
    obtain ⟨hsleft, _⟩ := image_eq_common_of_pushout_image_eq hts.symm
    refine ⟨s.toLeft, ?_, ?_⟩
    · change s.toLeft.image Sum.inl ∈ P.faces
      rwa [hsleft]
    · change s.toLeft.image Sum.inl = s.image pushoutLeftVertex
      calc
        s.toLeft.image Sum.inl = (s.toLeft.image Sum.inl).image pushoutLeftVertex := by
          rw [Finset.image_image]
          rfl
        _ = s.image pushoutLeftVertex := congrArg _ hsleft
  · rintro ⟨s, hs, rfl⟩
    have hsP : s.image Sum.inl ∈ P.faces := hs
    have hsQ : s.image Sum.inl ∈ Q.faces := by
      change s ∈ (commonVertexComplex Q).faces
      rwa [← hcommon]
    constructor
    · exact ⟨s.image Sum.inl, hsP, by dsimp only; rw [Finset.image_image]; rfl⟩
    · exact ⟨s.image Sum.inl, hsQ, by dsimp only; rw [Finset.image_image]; rfl⟩

theorem simplicialPushout_face_card_le (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) {n : ℕ}
    (hP : ∀ s ∈ P.faces, s.card ≤ n) (hQ : ∀ s ∈ Q.faces, s.card ≤ n) :
    ∀ s ∈ (standardRealization (simplicialPushout P Q)).faces, s.card ≤ n := by
  apply standardRealization_face_card_le
  rintro s (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · exact Finset.card_image_le.trans (hP t ht)
  · exact Finset.card_image_le.trans (hQ t ht)

def simplicialPushoutMap (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    (standardRealization P).space ⊕ (standardRealization Q).space →
      (standardRealization (simplicialPushout P Q)).space :=
  standardGluingMap (P.map pushoutLeftVertex) (Q.map pushoutRightVertex) ∘
    Sum.map (standardRelabelHomeomorph P pushoutLeftVertex pushoutLeftVertex_injective)
      (standardRelabelHomeomorph Q pushoutRightVertex pushoutRightVertex_injective)

theorem continuous_simplicialPushoutMap (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    Continuous (simplicialPushoutMap P Q) :=
  (continuous_standardGluingMap _ _).comp
    ((standardRelabelHomeomorph P pushoutLeftVertex pushoutLeftVertex_injective).continuous.sumMap
      (standardRelabelHomeomorph Q pushoutRightVertex pushoutRightVertex_injective).continuous)

theorem surjective_simplicialPushoutMap (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    Function.Surjective (simplicialPushoutMap P Q) :=
  (surjective_standardGluingMap _ _).comp
    (Sum.map_surjective.mpr ⟨
      (standardRelabelHomeomorph P pushoutLeftVertex pushoutLeftVertex_injective).surjective
      , (standardRelabelHomeomorph Q pushoutRightVertex pushoutRightVertex_injective).surjective⟩)

theorem isQuotientMap_simplicialPushoutMap (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    IsQuotientMap (simplicialPushoutMap P Q) :=
  IsQuotientMap.of_surjective_continuous (surjective_simplicialPushoutMap P Q)
    (continuous_simplicialPushoutMap P Q)

@[simp] theorem simplicialPushoutMap_inl_val (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) (x : (standardRealization P).space) :
    (simplicialPushoutMap P Q (Sum.inl x)).val = vertexPushforward pushoutLeftVertex x := rfl

@[simp] theorem simplicialPushoutMap_inr_val (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) (y : (standardRealization Q).space) :
    (simplicialPushoutMap P Q (Sum.inr y)).val = vertexPushforward pushoutRightVertex y := rfl

theorem simplicialPushoutMap_inl_injective (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    Function.Injective (fun x => simplicialPushoutMap P Q (Sum.inl x)) := by
  intro x y h
  exact Subtype.ext (vertexPushforward_injective _ pushoutLeftVertex_injective
    (congrArg Subtype.val h))

theorem simplicialPushoutMap_inr_injective (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    Function.Injective (fun y => simplicialPushoutMap P Q (Sum.inr y)) := by
  intro x y h
  exact Subtype.ext (vertexPushforward_injective _ pushoutRightVertex_injective
    (congrArg Subtype.val h))

theorem simplicialPushoutMap_inl_eq_inr_iff
    (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β))
    (hcommon : commonVertexComplex P = commonVertexComplex Q)
    (x : (standardRealization P).space) (y : (standardRealization Q).space) :
    simplicialPushoutMap P Q (Sum.inl x) = simplicialPushoutMap P Q (Sum.inr y) ↔
      ∃ z : (standardRealization (commonVertexComplex P)).space,
        vertexPushforward Sum.inl z = x.val ∧ vertexPushforward Sum.inl z = y.val := by
  constructor
  · intro h
    have hxy : vertexPushforward (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β)) x.val =
        vertexPushforward pushoutRightVertex y.val := congrArg Subtype.val h
    have hx := (vertexPushforward_image_space P
      (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β))).subset
      (mem_image_of_mem _ x.property)
    have hy := (vertexPushforward_image_space Q
      (pushoutRightVertex : ι ⊕ β → ι ⊕ (α ⊕ β))).subset
      (mem_image_of_mem _ y.property)
    have hz : vertexPushforward (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β)) x.val ∈
        (standardRealization ((commonVertexComplex P).map
          (Sum.inl : ι → ι ⊕ (α ⊕ β)))).space := by
      rw [← simplicialPushout_common P Q hcommon, standardRealization_space_inf]
      exact ⟨hx, hxy.symm ▸ hy⟩
    obtain ⟨z, hz, hzx⟩ := (vertexPushforward_image_space (commonVertexComplex P)
      (Sum.inl : ι → ι ⊕ (α ⊕ β))).symm.subset hz
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · apply vertexPushforward_injective
        (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β)) pushoutLeftVertex_injective
      rw [vertexPushforward_comp_apply]
      exact hzx
    · apply vertexPushforward_injective
        (pushoutRightVertex : ι ⊕ β → ι ⊕ (α ⊕ β)) pushoutRightVertex_injective
      rw [vertexPushforward_comp_apply]
      exact hzx.trans hxy
  · rintro ⟨z, hx, hy⟩
    apply Subtype.ext
    change vertexPushforward (pushoutLeftVertex : ι ⊕ α → ι ⊕ (α ⊕ β)) x.val =
      vertexPushforward pushoutRightVertex y.val
    rw [← hx, ← hy, vertexPushforward_comp_apply, vertexPushforward_comp_apply]
    rfl

def simplicialPushoutHomeomorph (P : PreAbstractSimplicialComplex (ι ⊕ α))
    (Q : PreAbstractSimplicialComplex (ι ⊕ β)) :
    Quotient (Setoid.ker (simplicialPushoutMap P Q)) ≃ₜ
      (standardRealization (simplicialPushout P Q)).space :=
  (isQuotientMap_simplicialPushoutMap P Q).homeomorph
    (f := ⟨simplicialPushoutMap P Q, continuous_simplicialPushoutMap P Q⟩)

end

end DifferentialGeometry.Topology.Engulfing
