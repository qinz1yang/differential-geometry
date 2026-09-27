import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Gluing
import Mathlib.Topology.Bases

section

set_option autoImplicit false

namespace Topology

variable {ι E : Type*} [TopologicalSpace E] [T2Space E]

theorem isClosed_sigma_prod_iff
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {s : Set ((Σ i, A i) × (Σ i, A i))} :
    IsClosed s ↔ ∀ i j, IsClosed
      {p : A i × A j | (⟨i, p.1⟩, ⟨j, p.2⟩) ∈ s} := by
  rw [← (Homeomorph.sigmaProdDistrib (X := A) (Y := Σ i, A i)).symm.isClosed_preimage,
    isClosed_sigma_iff]
  constructor
  · intro h i j
    have hi := h i
    rw [← (Homeomorph.prodComm (A i) (Σ j, A j)).symm.isClosed_preimage,
      ← (Homeomorph.sigmaProdDistrib (X := A) (Y := A i)).symm.isClosed_preimage,
      isClosed_sigma_iff] at hi
    have hij := hi j
    exact (Homeomorph.prodComm (A j) (A i)).isClosed_preimage.mp hij
  · intro h i
    rw [← (Homeomorph.prodComm (A i) (Σ j, A j)).symm.isClosed_preimage,
      ← (Homeomorph.sigmaProdDistrib (X := A) (Y := A i)).symm.isClosed_preimage,
      isClosed_sigma_iff]
    intro j
    exact (Homeomorph.prodComm (A j) (A i)).isClosed_preimage.mpr (h i j)

theorem isClosed_graph_relation_on_sigma
    (U V : Set E) (hUV : U ⊆ V)
    (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) V) :
    IsClosed {p : (Σ _ : ι, U) × (Σ _ : ι, U) |
      ∃ h : near p.1.1 p.2.1 = true,
        J ⟨(p.1.1, p.2.1), h⟩ p.1.2 = p.2.2} := by
  apply isClosed_sigma_prod_iff.mpr
  intro i j
  by_cases hij : near i j = true
  · have hc : Continuous (fun x : U => J ⟨(i, j), hij⟩ (x : E)) :=
      (hJ ⟨(i, j), hij⟩).comp_continuous continuous_subtype_val
        (fun x => hUV x.property)
    simpa [Function.comp_def, hij] using
      isClosed_eq (hc.comp continuous_fst) (continuous_subtype_val.comp continuous_snd)
  · have he : {p : U × U | ∃ h : near i j = true,
        J ⟨(i, j), h⟩ p.1 = p.2} = (∅ : Set (U × U)) := by
      ext p
      simp [hij]
    change IsClosed {p : U × U | ∃ h : near i j = true, J ⟨(i, j), h⟩ p.1 = p.2}
    rw [he]
    exact isClosed_empty

end Topology


end

section

open Topology TopologicalSpace

universe u

noncomputable section

namespace TopCat.GlueData

variable (D : TopCat.GlueData.{u})

theorem isOpenQuotientMap_sigma_ι :
    IsOpenQuotientMap (fun p : Σ i, D.U i => D.toGlueData.ι p.1 p.2) where
  surjective := by
    intro x
    obtain ⟨i, y, h⟩ := D.ι_jointly_surjective x
    exact ⟨⟨i, y⟩, h⟩
  continuous := continuous_sigma (fun i => (D.toGlueData.ι i).hom.continuous)
  isOpenMap := isOpenMap_sigma.mpr (fun i => (D.ι_isOpenEmbedding i).isOpenMap)

theorem t2Space_iff_isClosed_rel :
    T2Space D.toGlueData.glued ↔
      IsClosed {p : (Σ i, D.U i) × (Σ i, D.U i) | D.Rel p.1 p.2} := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_sigma_ι D)]
  have h : {q : (Σ i, D.U i) × (Σ i, D.U i) |
      D.toGlueData.ι q.1.1 q.1.2 = D.toGlueData.ι q.2.1 q.2.2} =
      {p : (Σ i, D.U i) × (Σ i, D.U i) | D.Rel p.1 p.2} := by
    ext p
    exact D.ι_eq_iff_rel p.1.1 p.2.1 p.1.2 p.2.2
  rw [h]

theorem secondCountableTopology [Countable D.J] [∀ i, SecondCountableTopology (D.U i)] :
    SecondCountableTopology D.toGlueData.glued :=
  (isOpenQuotientMap_sigma_ι D).isQuotientMap.secondCountableTopology
    (isOpenQuotientMap_sigma_ι D).isOpenMap

end TopCat.GlueData

end

end

section

open TopologicalSpace Topology

universe u

noncomputable section

namespace TopCat.GlueData

variable {ι E : Type u} [TopologicalSpace E]
    (U : Set E) (hU : IsOpen U) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U →
      J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))

def transitionOverlap (i j : ι) : Opens U :=
  ⟨{x | ∃ h : near i j = true, J ⟨(i, j), h⟩ x ∈ U}, by
    by_cases hij : near i j = true
    · have hc : Continuous (fun x : U => J ⟨(i, j), hij⟩ (x : E)) :=
        (hJ ⟨(i, j), hij⟩).comp_continuous continuous_subtype_val (fun x => x.property)
      simpa [Set.preimage, hij] using hU.preimage hc
    · convert isOpen_empty (X := U) using 1
      ext x
      simp [hij]⟩

def transitionMap (i j : ι) :
    (Opens.toTopCat (TopCat.of U)).obj (transitionOverlap U hU near J hJ i j) ⟶
      (Opens.toTopCat (TopCat.of U)).obj (transitionOverlap U hU near J hJ j i) :=
  ofHom ⟨fun x =>
    let h := x.property.choose
    let y := J ⟨(i, j), h⟩ x.val
    ⟨⟨y, x.property.choose_spec⟩, hsymm i j h, by
      change J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x.val) ∈ U
      rw [hinv i j h x.val x.val.property x.property.choose_spec]
      exact x.val.property⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    by_cases hij : near i j = true
    · have hc : Continuous (fun x : U => J ⟨(i, j), hij⟩ (x : E)) :=
        (hJ ⟨(i, j), hij⟩).comp_continuous continuous_subtype_val (fun x => x.property)
      exact hc.comp continuous_subtype_val
    · have : IsEmpty (transitionOverlap U hU near J hJ i j) :=
        ⟨fun x => hij x.property.choose⟩
      exact continuous_of_discreteTopology⟩

def ofTransitionMaps : TopCat.GlueData.{u} :=
  mk' {
    U := fun _ : ι => TopCat.of U
    V := transitionOverlap U hU near J hJ
    t := transitionMap U hU near J hJ hsymm hinv
    V_id := fun i => by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨hrefl i, by rw [hself i x x.property]; exact x.property⟩
    t_id := fun i => by
      funext x
      apply Subtype.ext
      apply Subtype.ext
      exact hself i x.val x.val.property
    t_inter := by
      intro i j k x hx
      obtain ⟨hij, hxj⟩ := x.property
      obtain ⟨hik, hxk⟩ := hx
      have hi : J ⟨(j, i), hsymm i j hij⟩ (J ⟨(i, j), hij⟩ x.val) = x.val :=
        hinv i j hij x.val x.val.property hxj
      obtain ⟨hjk, heq⟩ := htrans j i k (hsymm i j hij) hik
        (J ⟨(i, j), hij⟩ x.val) hxj (hi.symm ▸ x.val.property) (by simpa [hi] using hxk)
      exact ⟨hjk, by change J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x.val) ∈ U; rw [heq, hi]; exact hxk⟩
    cocycle := by
      intro i j k x hx
      apply Subtype.ext
      obtain ⟨hij, hxj⟩ := x.property
      obtain ⟨hik, hxk⟩ := hx
      have hji := hsymm i j hij
      have hi := hinv i j hij x.val x.val.property hxj
      obtain ⟨hjk, heq⟩ := htrans j i k hji hik (J ⟨(i, j), hij⟩ x.val)
        hxj (hi.symm ▸ x.val.property) (by simpa [hi] using hxk)
      change J ⟨(j, k), _⟩ (J ⟨(i, j), _⟩ x.val) = J ⟨(i, k), _⟩ x.val
      simpa [hi] using heq }

end TopCat.GlueData

end

end

section

open Topology TopologicalSpace
universe u
noncomputable section
namespace TopCat.GlueData
variable {ι E : Type u} [TopologicalSpace E]
    (U : Set E) (hU : IsOpen U) (near : ι → ι → Bool)
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hJ : ∀ a, ContinuousOn (J a) U)
    (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hself : ∀ i x, x ∈ U → J ⟨(i, i), hrefl i⟩ x = x)
    (hinv : ∀ i j (h : near i j = true) x, x ∈ U → J ⟨(i, j), h⟩ x ∈ U → J ⟨(j, i), hsymm i j h⟩ (J ⟨(i, j), h⟩ x) = x)
    (htrans : ∀ i j k (hij : near i j = true) (hjk : near j k = true) x,
      x ∈ U → J ⟨(i, j), hij⟩ x ∈ U → J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x) ∈ U →
      ∃ hik : near i k = true,
        J ⟨(i, k), hik⟩ x = J ⟨(j, k), hjk⟩ (J ⟨(i, j), hij⟩ x))

theorem rel_iff_graph (i j : ι) (x y : U) :
   (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).Rel ⟨i,x⟩ ⟨j,y⟩ ↔
    ∃ h : near i j = true, J ⟨(i,j),h⟩ x = y := by
  unfold ofTransitionMaps
  dsimp [mk', Rel]
  constructor
  · rintro ⟨z, hz1, hz2⟩
    obtain ⟨h, hz⟩ := z.property
    refine ⟨h, ?_⟩
    change z.val = x at hz1
    change (⟨J ⟨(i, j), h⟩ z.val, hz⟩ : U) = y at hz2
    rw [← hz1]
    exact congrArg Subtype.val hz2
  · rintro ⟨h, heq⟩
    refine ⟨⟨x, ⟨h, heq ▸ y.property⟩⟩, rfl, ?_⟩
    apply Subtype.ext
    exact heq

theorem t2Space_ofTransitionMaps [T2Space E] :
    T2Space (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).toGlueData.glued := by
  rw [t2Space_iff_isClosed_rel]
  have he : {p : (Σ _ : ι, U) × (Σ _ : ι, U) |
      (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).Rel p.1 p.2} =
      {p : (Σ _ : ι, U) × (Σ _ : ι, U) |
        ∃ h : near p.1.1 p.2.1 = true, J ⟨(p.1.1,p.2.1),h⟩ p.1.2 = p.2.2} := by
    ext p
    exact rel_iff_graph U hU near J hJ hrefl hsymm hself hinv htrans p.1.1 p.2.1 p.1.2 p.2.2
  change IsClosed {p : (Σ _ : ι, U) × (Σ _ : ι, U) |
    (ofTransitionMaps U hU near J hJ hrefl hsymm hself hinv htrans).Rel p.1 p.2}
  rw [he]
  exact Topology.isClosed_graph_relation_on_sigma U U (Set.Subset.refl U) near J hJ

end TopCat.GlueData

end

end

section

open Topology

universe u v

noncomputable section

namespace TopCat.GlueData

variable (D : TopCat.GlueData.{u}) {X : Type v} [TopologicalSpace X]
    (f : ∀ i, D.U i → X)

private def unionMap (z : D.toGlueData.glued) : X :=
  f (D.ι_jointly_surjective z).choose (D.ι_jointly_surjective z).choose_spec.choose

variable (hrel : ∀ i j x y, f i x = f j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩)

include hrel

omit [TopologicalSpace X] in
private theorem unionMap_ι (i : D.J) (x : D.U i) :
    D.unionMap f (D.toGlueData.ι i x) = f i x := by
  apply (hrel _ _ _ _).mpr
  exact (D.ι_eq_iff_rel _ _ _ _).mp
    (D.ι_jointly_surjective (D.toGlueData.ι i x)).choose_spec.choose_spec

omit [TopologicalSpace X] in
private theorem range_unionMap : Set.range (D.unionMap f) = ⋃ i, Set.range (f i) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective z
    rw [D.unionMap_ι f hrel]
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self _⟩
  · intro hx
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨D.toGlueData.ι i y, D.unionMap_ι f hrel i y⟩

omit [TopologicalSpace X] in
private theorem unionMap_injective : Function.Injective (D.unionMap f) := by
  intro x y hxy
  obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective y
  rw [D.unionMap_ι f hrel, D.unionMap_ι f hrel] at hxy
  exact (D.ι_eq_iff_rel i j x y).mpr ((hrel i j x y).mp hxy)

variable (hf : ∀ i, IsOpenEmbedding (f i))

include hf

private theorem unionMap_continuous : Continuous (D.unionMap f) := by
  apply (D.isOpenQuotientMap_sigma_ι).continuous_comp_iff.mp
  apply continuous_sigma
  intro i
  simpa only [Function.comp_apply, D.unionMap_ι f hrel] using (hf i).continuous

private theorem unionMap_isOpenMap : IsOpenMap (D.unionMap f) := by
  apply (D.isOpenQuotientMap_sigma_ι).isOpenMap_iff.mpr
  apply isOpenMap_sigma.mpr
  intro i
  simpa only [Function.comp_apply, D.unionMap_ι f hrel] using (hf i).isOpenMap

def homeomorphUnion : D.toGlueData.glued ≃ₜ (⋃ i, Set.range (f i) : Set X) := by
  let F : D.toGlueData.glued → (⋃ i, Set.range (f i) : Set X) :=
    fun z => ⟨D.unionMap f z, (D.range_unionMap f hrel).le (Set.mem_range_self z)⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      exact D.unionMap_injective f hrel (congr_arg Subtype.val h)
    · intro x
      obtain ⟨z, hz⟩ := (D.range_unionMap f hrel).ge x.property
      exact ⟨z, Subtype.ext hz⟩
  exact (Equiv.ofBijective F hF).toHomeomorphOfContinuousOpen
    ((D.unionMap_continuous f hrel hf).subtype_mk _)
    ((D.unionMap_isOpenMap f hrel hf).subtype_mk _)

@[simp]
theorem homeomorphUnion_ι (i : D.J) (x : D.U i) :
    ↑(D.homeomorphUnion f hrel hf (D.toGlueData.ι i x)) = f i x :=
  D.unionMap_ι f hrel i x

@[simp]
theorem homeomorphUnion_symm_apply (i : D.J) (x : D.U i) :
    (D.homeomorphUnion f hrel hf).symm
      ⟨f i x, Set.mem_iUnion.mpr ⟨i, Set.mem_range_self x⟩⟩ = D.toGlueData.ι i x := by
  apply (D.homeomorphUnion f hrel hf).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (D.homeomorphUnion_ι f hrel hf i x).symm

end TopCat.GlueData

end

end
