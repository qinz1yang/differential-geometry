import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Maps.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace DifferentialGeometry.TopCat.Pushout

variable {A D X P : TopCat.{u}} {f : A ⟶ D} {g : A ⟶ X}
  {r : D ⟶ P} {b : X ⟶ P} (h : IsPushout f g r b)

include h


theorem isOpen_iff_preimages (s : Set P) :
    IsOpen s ↔ IsOpen (r ⁻¹' s) ∧ IsOpen (b ⁻¹' s) := by
  refine (_root_.TopCat.isOpen_iff_of_isColimit h.cocone h.isColimit s).trans ?_
  constructor
  · intro hs
    exact ⟨hs WalkingSpan.left, hs WalkingSpan.right⟩
  · rintro ⟨hr, hb⟩ j
    rcases j with (_ | (_ | _))
    · exact hr.preimage f.hom.continuous
    · exact hr
    · exact hb


theorem isClosed_iff_preimages (s : Set P) :
    IsClosed s ↔ IsClosed (r ⁻¹' s) ∧ IsClosed (b ⁻¹' s) := by
  simpa only [← isOpen_compl_iff, Set.preimage_compl] using isOpen_iff_preimages h sᶜ


theorem jointly_surjective (p : P) : (∃ d, r d = p) ∨ ∃ x, b x = p :=
  Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) p

theorem inl_eq_inr_iff (hf : Function.Injective f) (d : D) (x : X) :
    r d = b x ↔ ∃ a, f a = d ∧ g a = x :=
  Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    (h.map (forget TopCat)).isColimit hf d x


theorem injective_inr (hf : Function.Injective f) : Function.Injective b :=
  Types.pushoutCocone_inr_injective_of_isColimit (h.map (forget TopCat)).isColimit hf

theorem preimage_inl_image_inr (hf : Function.Injective f) (s : Set X) :
    r ⁻¹' (b '' s) = f '' (g ⁻¹' s) := by
  ext d
  constructor
  · rintro ⟨x, hx, hxd⟩
    obtain ⟨a, ha, hax⟩ := (inl_eq_inr_iff h hf d x).mp hxd.symm
    exact ⟨a, show g a ∈ s from hax.symm ▸ hx, ha⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨g a, ha, (ConcreteCategory.congr_hom h.w a).symm⟩

theorem isClosedEmbedding_inr (hf : IsClosedEmbedding f) : IsClosedEmbedding b := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap b.hom.continuous
    (injective_inr h hf.injective)
  intro s hs
  rw [isClosed_iff_preimages h, preimage_inl_image_inr h hf.injective,
    Set.preimage_image_eq _ (injective_inr h hf.injective)]
  exact ⟨hf.isClosedMap _ (hs.preimage g.hom.continuous), hs⟩

theorem inl_eq_inl_iff (hf : Function.Injective f) (d e : D) :
    r d = r e ↔ d = e ∨ ∃ a a', g a = g a' ∧ d = f a ∧ e = f a' := by
  let ht := h.map (forget TopCat)
  let ft := (forget TopCat).map f
  let gt := (forget TopCat).map g
  let hc := IsPushout.of_isColimit (Types.Pushout.isColimitCocone ft gt)
  let i := ht.isoIsPushout _ _ hc
  have hi (d : D) : i.hom (r d) = Types.Pushout.inl ft gt d :=
    ConcreteCategory.congr_hom (ht.inl_isoIsPushout_hom _ _ hc) d
  have heq : r d = r e ↔ Types.Pushout.inl ft gt d = Types.Pushout.inl ft gt e := by
    constructor
    · intro he
      rw [← hi, ← hi, he]
    · intro he
      apply (CategoryTheory.isIso_iff_bijective i.hom).mp (inferInstance : IsIso i.hom) |>.1
      rwa [hi, hi]
  rw [heq]
  have : Mono ft := (CategoryTheory.mono_iff_injective ft).mpr hf
  simpa only [exists_prop] using!
    (Types.Pushout.quot_mk_eq_iff ft gt (Sum.inl d) (Sum.inl e)).trans
      (Types.Pushout.inl_rel'_inl_iff ft gt d e)


theorem injOn_inl_compl (hf : Function.Injective f) :
    Set.InjOn r (Set.range f)ᶜ := by
  intro d hd e _ he
  rcases (inl_eq_inl_iff h hf d e).mp he with he | ⟨a, _, _, ha, _⟩
  · exact he
  · exact (hd ⟨a, ha.symm⟩).elim

theorem preimage_inl_range_inr (hf : Function.Injective f) :
    r ⁻¹' Set.range b = Set.range f := by
  simpa using preimage_inl_image_inr h hf Set.univ

theorem image_inl_compl (hf : Function.Injective f) :
    r '' (Set.range f)ᶜ = (Set.range b)ᶜ := by
  ext p
  constructor
  · rintro ⟨d, hd, rfl⟩ hp
    exact hd (by simpa [← preimage_inl_range_inr h hf] using hp)
  · intro hp
    rcases jointly_surjective h p with ⟨d, rfl⟩ | ⟨x, hx⟩
    · refine ⟨d, ?_, rfl⟩
      intro hd
      exact hp (by simpa [← preimage_inl_range_inr h hf] using hd)
    · exact (hp ⟨x, hx⟩).elim


def inlComplement : C({d : D // d ∉ Set.range f}, P) :=
  ⟨fun d ↦ r d.val, r.hom.continuous.comp continuous_subtype_val⟩


theorem isOpenEmbedding_inlComplement (hf : IsClosedEmbedding f) :
    IsOpenEmbedding (inlComplement (f := f) (r := r)) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (inlComplement (f := f) (r := r)).continuous
    (fun d e he ↦ Subtype.ext (injOn_inl_compl h hf.injective d.property e.property he))
  intro s hs
  apply (isOpen_iff_preimages h _).mpr
  constructor
  · have heq : r ⁻¹' (inlComplement (f := f) (r := r) '' s) = Subtype.val '' s := by
      ext d
      constructor
      · rintro ⟨e, he, hed⟩
        rcases (inl_eq_inl_iff h hf.injective e.val d).mp hed with hd | ⟨a, _, _, ha, _⟩
        · exact ⟨e, he, hd⟩
        · exact (e.property ⟨a, ha.symm⟩).elim
      · rintro ⟨e, he, rfl⟩
        exact ⟨e, he, rfl⟩
    rw [heq]
    exact hf.isClosed_range.isOpen_compl.isOpenMap_subtype_val s hs
  · have heq : b ⁻¹' (inlComplement (f := f) (r := r) '' s) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨d, _, hdx⟩
      obtain ⟨a, ha, _⟩ := (inl_eq_inr_iff h hf.injective d.val x).mp hdx
      exact d.property ⟨a, ha⟩
    rw [heq]
    exact isOpen_empty

theorem range_inlComplement (hf : Function.Injective f) :
    Set.range (inlComplement (f := f) (r := r)) = (Set.range b)ᶜ := by
  rw [← image_inl_compl h hf]
  ext p
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d.val, d.property, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩


theorem isQuotientMap_sumElim : IsQuotientMap (Sum.elim r b) := by
  refine ⟨?_, ?_⟩
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro s
    rw [isOpen_sum_iff, isOpen_iff_preimages h]
    rfl
  · intro p
    rcases jointly_surjective h p with ⟨d, hd⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl d, hd⟩
    · exact ⟨Sum.inr x, hx⟩

end DifferentialGeometry.TopCat.Pushout
