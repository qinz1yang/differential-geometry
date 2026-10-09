import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set _root_.Topology _root_.Geometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def standardRealization (P : PreAbstractSimplicialComplex ι) :
    SimplicialComplex ℝ (ι → ℝ) := by
  classical
  apply SimplicialComplex.ofAffineIndependent
    (P.map (fun i => Pi.single i (1 : ℝ)))
  apply (Pi.basisFun ℝ ι).linearIndependent.affineIndependent.range.mono
  intro x hx
  obtain ⟨s, ⟨t, ht, rfl⟩, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, Pi.basisFun_apply ℝ ι i⟩

theorem standardRealization_mem_space (P : PreAbstractSimplicialComplex ι) (x : ι → ℝ) :
    x ∈ (standardRealization P).space ↔
      ∃ s ∈ P.faces, x ∈ convexHull ℝ ((s.image (fun i => Pi.single i (1 : ℝ)) : Finset (ι → ℝ)) : Set (ι → ℝ)) := by
  rw [SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hx⟩
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨_, ⟨t, ht, rfl⟩, hx⟩

theorem standardRealization_finite_faces (P : PreAbstractSimplicialComplex ι) :
    (standardRealization P).faces.Finite := by
  exact P.faces.toFinite.image _

theorem standardRealization_mono {P Q : PreAbstractSimplicialComplex ι} (hPQ : P ≤ Q) :
    (standardRealization P).space ⊆ (standardRealization Q).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (standardRealization_mem_space P x).mp hx
  exact (standardRealization_mem_space Q x).mpr ⟨s, hPQ hs, hxs⟩

theorem standardRealization_face_card_le (P : PreAbstractSimplicialComplex ι) {n : ℕ}
    (hn : ∀ s ∈ P.faces, s.card ≤ n) :
    ∀ s ∈ (standardRealization P).faces, s.card ≤ n := by
  rintro s ⟨t, ht, rfl⟩
  exact (Finset.card_image_le).trans (hn t ht)

theorem standardRealization_space_sup (P Q : PreAbstractSimplicialComplex ι) :
    (standardRealization (P ⊔ Q)).space =
      (standardRealization P).space ∪ (standardRealization Q).space := by
  ext x
  simp only [standardRealization_mem_space, mem_union]
  change (∃ s, (s ∈ P.faces ∨ s ∈ Q.faces) ∧ _) ↔ _
  aesop

theorem standardRealization_space_inf (P Q : PreAbstractSimplicialComplex ι) :
    (standardRealization (P ⊓ Q)).space =
      (standardRealization P).space ∩ (standardRealization Q).space := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := (standardRealization_mem_space _ _).mp hx
    exact ⟨(standardRealization_mem_space _ _).mpr ⟨s, hs.1, hx⟩,
      (standardRealization_mem_space _ _).mpr ⟨s, hs.2, hx⟩⟩
  · rintro ⟨hxP, hxQ⟩
    obtain ⟨s, hs, hxs⟩ := (standardRealization_mem_space _ _).mp hxP
    obtain ⟨t, ht, hxt⟩ := (standardRealization_mem_space _ _).mp hxQ
    let e : ι → (ι → ℝ) := fun i => Pi.single i 1
    have he : Function.Injective e := by
      intro i j hij
      apply (Pi.basisFun ℝ ι).linearIndependent.injective
      simpa only [Pi.basisFun_apply] using hij
    have hsR : s.image e ∈ (standardRealization (P ⊔ Q)).faces := ⟨s, Or.inl hs, rfl⟩
    have htR : t.image e ∈ (standardRealization (P ⊔ Q)).faces := ⟨t, Or.inr ht, rfl⟩
    have hxst := (standardRealization (P ⊔ Q)).inter_subset_convexHull hsR htR ⟨hxs, hxt⟩
    have himg : ((s.image e : Finset (ι → ℝ)) : Set (ι → ℝ)) ∩
        (t.image e : Set (ι → ℝ)) = ((s ∩ t).image e : Set (ι → ℝ)) := by
      ext y
      simp only [mem_inter_iff, Finset.mem_coe, Finset.mem_image, Finset.mem_inter]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, heq⟩⟩
        have hji := he heq
        subst j
        exact ⟨i, ⟨hi, hj⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hj⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, ⟨i, hj, rfl⟩⟩
    rw [himg] at hxst
    have hne : (s ∩ t).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hxst
      simp at hxst
    exact (standardRealization_mem_space _ _).mpr ⟨s ∩ t,
      ⟨(P.isRelLowerSet_faces hs).2 Finset.inter_subset_left hne,
        (Q.isRelLowerSet_faces ht).2 Finset.inter_subset_right hne⟩, hxst⟩

theorem isCompact_standardRealization_space (P : PreAbstractSimplicialComplex ι) :
    IsCompact (standardRealization P).space := by
  exact (standardRealization_finite_faces P).isCompact_biUnion
    (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)

instance compactSpace_standardRealization (P : PreAbstractSimplicialComplex ι) :
    CompactSpace (standardRealization P).space :=
  isCompact_iff_compactSpace.mp (isCompact_standardRealization_space P)

def standardGluingMap (P Q : PreAbstractSimplicialComplex ι) :
    (standardRealization P).space ⊕ (standardRealization Q).space →
      (standardRealization (P ⊔ Q)).space :=
  Sum.elim (fun x => ⟨x, (standardRealization_space_sup P Q).symm ▸ Or.inl x.property⟩)
    (fun x => ⟨x, (standardRealization_space_sup P Q).symm ▸ Or.inr x.property⟩)

theorem continuous_standardGluingMap (P Q : PreAbstractSimplicialComplex ι) :
    Continuous (standardGluingMap P Q) := by
  apply Continuous.sumElim <;> exact continuous_subtype_val.subtype_mk _

theorem surjective_standardGluingMap (P Q : PreAbstractSimplicialComplex ι) :
    Function.Surjective (standardGluingMap P Q) := by
  intro x
  have hx := (standardRealization_space_sup P Q).subset x.property
  rcases hx with hx | hx
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

theorem isQuotientMap_standardGluingMap (P Q : PreAbstractSimplicialComplex ι) :
    IsQuotientMap (standardGluingMap P Q) :=
  IsQuotientMap.of_surjective_continuous (surjective_standardGluingMap P Q)
    (continuous_standardGluingMap P Q)

theorem standardGluingMap_inl_eq_inr_iff (P Q : PreAbstractSimplicialComplex ι)
    (x : (standardRealization P).space) (y : (standardRealization Q).space) :
    standardGluingMap P Q (Sum.inl x) = standardGluingMap P Q (Sum.inr y) ↔
      ∃ z : (standardRealization (P ⊓ Q)).space, z.val = x.val ∧ z.val = y.val := by
  constructor
  · intro h
    have hxy : x.val = y.val := congrArg Subtype.val h
    refine ⟨⟨x, (standardRealization_space_inf P Q).symm ▸ ⟨x.property, ?_⟩⟩, rfl, hxy⟩
    exact hxy ▸ y.property
  · rintro ⟨z, hzx, hzy⟩
    exact Subtype.ext (hzx.symm.trans hzy)

def standardGluingHomeomorph (P Q : PreAbstractSimplicialComplex ι) :
    Quotient (Setoid.ker (standardGluingMap P Q)) ≃ₜ (standardRealization (P ⊔ Q)).space :=
  (isQuotientMap_standardGluingMap P Q).homeomorph
    (f := ⟨standardGluingMap P Q, continuous_standardGluingMap P Q⟩)

section Relabel

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def vertexPushforward (q : ι → κ) : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) :=
  Fintype.linearCombination ℝ (fun i => Pi.single (q i) 1)

omit [Fintype κ] in
@[simp] theorem vertexPushforward_single (q : ι → κ) (i : ι) :
    vertexPushforward q (Pi.single i 1) = Pi.single (q i) 1 := by
  simp [vertexPushforward, Fintype.linearCombination_apply]

omit [DecidableEq ι] [Fintype κ] in
theorem vertexPushforward_apply_at (q : ι → κ) (hq : Function.Injective q)
    (x : ι → ℝ) (i : ι) : vertexPushforward q x (q i) = x i := by
  classical
  simp [vertexPushforward, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, hq.eq_iff]

omit [DecidableEq ι] [Fintype κ] in
theorem vertexPushforward_injective (q : ι → κ) (hq : Function.Injective q) :
    Function.Injective (vertexPushforward q) := by
  classical
  intro x y hxy
  funext i
  have h := congrFun hxy (q i)
  simpa only [vertexPushforward_apply_at q hq] using h

omit [DecidableEq ι] in
theorem vertexPushforward_comp {τ : Type*} [DecidableEq τ]
    (q : ι → κ) (r : κ → τ) :
    (vertexPushforward r).comp (vertexPushforward q) = vertexPushforward (r ∘ q) := by
  classical
  apply (Pi.basisFun ℝ ι).ext
  intro i
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, vertexPushforward_single,
    Function.comp_apply]

omit [DecidableEq ι] in
theorem vertexPushforward_comp_apply {τ : Type*} [DecidableEq τ]
    (q : ι → κ) (r : κ → τ) (x : ι → ℝ) :
    vertexPushforward r (vertexPushforward q x) = vertexPushforward (r ∘ q) x := by
  classical
  exact LinearMap.congr_fun (vertexPushforward_comp q r) x

theorem vertexPushforward_image_face (q : ι → κ) (s : Finset ι) :
    vertexPushforward q '' convexHull ℝ ((s.image (fun i => Pi.single i (1 : ℝ))) : Set (ι → ℝ)) =
      convexHull ℝ (((s.image q).image (fun j => Pi.single j (1 : ℝ))) : Set (κ → ℝ)) := by
  rw [LinearMap.image_convexHull]
  congr 1
  ext x
  simp only [mem_image, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨q i, ⟨i, hi, rfl⟩, (vertexPushforward_single q i).symm⟩
  · rintro ⟨j, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨Pi.single i 1, ⟨i, hi, rfl⟩, vertexPushforward_single q i⟩

theorem vertexPushforward_image_space (P : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    vertexPushforward q '' (standardRealization P).space = (standardRealization (P.map q)).space := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hx⟩ := (standardRealization_mem_space P x).mp hx
    apply (standardRealization_mem_space _ _).mpr
    refine ⟨s.image q, ⟨s, hs, rfl⟩, ?_⟩
    rw [← vertexPushforward_image_face]
    exact mem_image_of_mem _ hx
  · intro hy
    obtain ⟨t, ⟨s, hs, rfl⟩, hy⟩ := (standardRealization_mem_space _ _).mp hy
    rw [← vertexPushforward_image_face] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, (standardRealization_mem_space _ _).mpr ⟨s, hs, hx⟩, rfl⟩

def standardRelabelHomeomorph (P : PreAbstractSimplicialComplex ι)
    (q : ι → κ) (hq : Function.Injective q) :
    (standardRealization P).space ≃ₜ (standardRealization (P.map q)).space := by
  let f : (standardRealization P).space → (standardRealization (P.map q)).space :=
    fun x => ⟨vertexPushforward q x,
      (vertexPushforward_image_space P q).subset (mem_image_of_mem _ x.property)⟩
  have hf : Continuous f :=
    ((vertexPushforward q).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := fun x y h =>
    Subtype.ext (vertexPushforward_injective q hq (congrArg Subtype.val h))
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (vertexPushforward_image_space P q).symm.subset y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩) hf

def standardVertexMap (P : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    (standardRealization P).space → (standardRealization (P.map q)).space :=
  fun x => ⟨vertexPushforward q x,
    (vertexPushforward_image_space P q).subset (mem_image_of_mem _ x.property)⟩

theorem continuous_standardVertexMap (P : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    Continuous (standardVertexMap P q) :=
  ((vertexPushforward q).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

theorem surjective_standardVertexMap (P : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    Function.Surjective (standardVertexMap P q) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := (vertexPushforward_image_space P q).symm.subset y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem isQuotientMap_standardVertexMap (P : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    IsQuotientMap (standardVertexMap P q) :=
  IsQuotientMap.of_surjective_continuous (surjective_standardVertexMap P q)
    (continuous_standardVertexMap P q)

def standardVertexQuotientHomeomorph (P : PreAbstractSimplicialComplex ι) (q : ι → κ) :
    Quotient (Setoid.ker (standardVertexMap P q)) ≃ₜ (standardRealization (P.map q)).space :=
  (isQuotientMap_standardVertexMap P q).homeomorph
    (f := ⟨standardVertexMap P q, continuous_standardVertexMap P q⟩)

end Relabel

end

end DifferentialGeometry.Topology.Engulfing
