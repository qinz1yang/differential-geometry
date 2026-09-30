import DifferentialGeometry.Topology.Quotient.SameFibers
import Mathlib.Topology.Maps.Proper.Basic

namespace DifferentialGeometry.Topology

open Set _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [T2Space Y]

theorem exists_closedEmbedding_restoreFiber {f : X → Y} {K : Set X}
    (hf : Continuous f) (hfK : collapsesExactly f K) (h : Y ≃ₜ Y)
    {V : Set Y} (hV : IsOpen V) (hKV : f '' K ⊆ V)
    (hfix : ∀ y ∈ V, h y = y) (hrange : h '' range f ⊆ range f) :
    ∃ g : X → X, IsClosedEmbedding g ∧
      (∀ x, f (g x) = h (f x)) ∧
      (∀ x, f x ∈ V → g x = x) ∧
      (∀ x, g x ∈ K ↔ x ∈ K) ∧
      range g = f ⁻¹' (h '' range f) := by
  classical
  have hlift (x : X) : ∃ y, f y = h (f x) :=
    hrange ⟨f x, mem_range_self x, rfl⟩
  let lift : X → X := fun x => Classical.choose (hlift x)
  have hlift_eq (x : X) : f (lift x) = h (f x) := Classical.choose_spec (hlift x)
  let g : X → X := fun x => if f x ∈ V then x else lift x
  have hgfix (x : X) (hx : f x ∈ V) : g x = x := ite_eq_left hx
  have hgfixK (x : X) (hx : x ∈ K) : g x = x :=
    hgfix x (hKV ⟨x, hx, rfl⟩)
  have hgf (x : X) : f (g x) = h (f x) := by
    by_cases hx : f x ∈ V
    · rw [hgfix x hx, hfix _ hx]
    · exact (congrArg f (ite_eq_right hx)).trans (hlift_eq x)
  have hpreV (y : Y) (hy : h y ∈ V) : y ∈ V := by
    have he : h y = y := h.injective (hfix (h y) hy)
    exact he ▸ hy
  have hgK (x : X) : g x ∈ K ↔ x ∈ K := by
    constructor
    · intro hx
      have hv : h (f x) ∈ V := hgf x ▸ hKV ⟨g x, hx, rfl⟩
      rwa [hgfix x (hpreV _ hv)] at hx
    · intro hx
      rwa [hgfixK x hx]
  have hginj : Function.Injective g := by
    intro x y hxy
    have he : f x = f y := h.injective (by rw [← hgf x, ← hgf y, hxy])
    rcases (hfK x y).mp he with he | ⟨hx, hy⟩
    · exact he
    · rwa [hgfixK x hx, hgfixK y hy] at hxy
  have hgraph : g.graph =
      {p : X × X | f p.2 = h (f p.1)} ∩
        ({p : X × X | f p.1 ∉ V} ∪ {p : X × X | p.2 = p.1}) := by
    ext ⟨x, y⟩
    change g x = y ↔ f y = h (f x) ∧ (f x ∉ V ∨ y = x)
    constructor
    · rintro rfl
      refine ⟨hgf x, ?_⟩
      by_cases hx : f x ∈ V
      · exact Or.inr (hgfix x hx)
      · exact Or.inl hx
    · rintro ⟨hfxy, hxy⟩
      by_cases hx : f x ∈ V
      · exact (hgfix x hx).trans (hxy.resolve_left (not_not.mpr hx)).symm
      · rcases (hfK (g x) y).mp ((hgf x).trans hfxy.symm) with he | ⟨hgx, _⟩
        · exact he
        · exact (hx (hKV ⟨x, (hgK x).mp hgx, rfl⟩)).elim
  have hgcont : Continuous g := by
    apply continuous_of_isClosed_graph
    rw [hgraph]
    exact (isClosed_eq (hf.comp continuous_snd)
      (h.continuous.comp (hf.comp continuous_fst))).inter
        ((hV.preimage (hf.comp continuous_fst)).isClosed_compl.union
          (isClosed_eq continuous_snd continuous_fst))
  refine ⟨g, hgcont.isClosedEmbedding hginj, hgf, hgfix, hgK, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, mem_range_self x, (hgf x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, he⟩
    by_cases hz : z ∈ K
    · exact ⟨z, hgfixK z hz⟩
    · refine ⟨x, ?_⟩
      exact ((hfK (g x) z).mp ((hgf x).trans he)).resolve_right (fun hk => hz hk.2)

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [T2Space Y] in
theorem image_preimage_of_restored_range {f : X → Y} {g : X → X} (h : Y ≃ₜ Y)
    (hgf : ∀ x, f (g x) = h (f x)) (hrange : range g = f ⁻¹' (h '' range f))
    (S : Set Y) : g '' (f ⁻¹' S) = f ⁻¹' (h '' (S ∩ range f)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨hx, mem_range_self x⟩, (hgf x).symm⟩
  · rintro ⟨y, ⟨hyS, hyf⟩, hyz⟩
    have hzg : z ∈ range g := by
      rw [hrange]
      exact ⟨y, hyf, hyz⟩
    obtain ⟨x, rfl⟩ := hzg
    refine ⟨x, ?_, rfl⟩
    have he : y = f x := h.injective (hyz.trans (hgf x))
    change f x ∈ S
    exact he ▸ hyS

omit [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T2Space Y] in
theorem collapsesExactly.preimage_image_eq_of_subset {f : X → Y} {K S : Set X}
    (hfK : collapsesExactly f K) (hKS : K ⊆ S) : f ⁻¹' (f '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfK y x).mp hxy with rfl | ⟨_, hx⟩
    · exact hy
    · exact hKS hx
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [T2Space Y] in
theorem image_of_restored_range {f : X → Y} {g : X → X} {K S : Set X}
    (hfK : collapsesExactly f K) (hKS : K ⊆ S) (h : Y ≃ₜ Y)
    (hgf : ∀ x, f (g x) = h (f x)) (hrange : range g = f ⁻¹' (h '' range f)) :
    g '' S = f ⁻¹' (h '' (f '' S)) := by
  have hh := image_preimage_of_restored_range h hgf hrange (f '' S)
  rw [hfK.preimage_image_eq_of_subset hKS,
    inter_eq_left.mpr (image_subset_range f S)] at hh
  exact hh

omit [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T2Space Y] in
theorem preimage_image_eq_of_two_fibers {f : X → Y} {A B S : Set X}
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hAS : A ⊆ S) (hBS : B ⊆ S) : f ⁻¹' (f '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfAB y x).mp hxy with rfl | ⟨_, hx⟩ | ⟨_, hx⟩
    · exact hy
    · exact hAS hx
    · exact hBS hx
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [T2Space Y] in
theorem image_of_restored_range_two {f : X → Y} {g : X → X} {A B S : Set X}
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hAS : A ⊆ S) (hBS : B ⊆ S) (h : Y ≃ₜ Y)
    (hgf : ∀ x, f (g x) = h (f x)) (hrange : range g = f ⁻¹' (h '' range f)) :
    g '' S = f ⁻¹' (h '' (f '' S)) := by
  have hh := image_preimage_of_restored_range h hgf hrange (f '' S)
  rw [preimage_image_eq_of_two_fibers hfAB hAS hBS,
    inter_eq_left.mpr (image_subset_range f S)] at hh
  exact hh

omit [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T2Space Y] in
theorem collapsesExactly.comp_injective {Z : Type*} {f : X → Y} {c : Y → Z} {K : Set X}
    (hfK : collapsesExactly f K) (hc : Function.Injective c) :
    collapsesExactly (c ∘ f) K :=
  fun x y => hc.eq_iff.trans (hfK x y)

theorem exists_continuous_restoreFirstFiber {f : X → Y} {A B : Set X}
    (hf : Continuous f)
    (hfAB : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (hAB : Disjoint A B) (h : Y ≃ₜ Y)
    {V : Set Y} (hV : IsOpen V) (hAV : f '' A ⊆ V)
    (hfix : ∀ y ∈ V, h y = y) (hrange : h '' range f ⊆ range f)
    (havoid : Disjoint (h '' range f) (f '' B)) :
    ∃ g : X → X, Continuous g ∧ collapsesExactly g B ∧
      (∀ x, f (g x) = h (f x)) ∧
      (∀ x, f x ∈ V → g x = x) ∧
      (∀ x, g x ∈ A ↔ x ∈ A) ∧
      (∀ x, g x ∉ B) ∧
      range g = f ⁻¹' (h '' range f) := by
  classical
  have hlift (x : X) : ∃ y, f y = h (f x) :=
    hrange ⟨f x, mem_range_self x, rfl⟩
  let lift : X → X := fun x => Classical.choose (hlift x)
  have hlift_eq (x : X) : f (lift x) = h (f x) := Classical.choose_spec (hlift x)
  let g : X → X := fun x => if f x ∈ V then x else lift x
  have hgfix (x : X) (hx : f x ∈ V) : g x = x := ite_eq_left hx
  have hgfixA (x : X) (hx : x ∈ A) : g x = x :=
    hgfix x (hAV ⟨x, hx, rfl⟩)
  have hgf (x : X) : f (g x) = h (f x) := by
    by_cases hx : f x ∈ V
    · rw [hgfix x hx, hfix _ hx]
    · exact (congrArg f (ite_eq_right hx)).trans (hlift_eq x)
  have hpreV (y : Y) (hy : h y ∈ V) : y ∈ V := by
    have he : h y = y := h.injective (hfix (h y) hy)
    exact he ▸ hy
  have hgA (x : X) : g x ∈ A ↔ x ∈ A := by
    constructor
    · intro hx
      have hv : h (f x) ∈ V := hgf x ▸ hAV ⟨g x, hx, rfl⟩
      rwa [hgfix x (hpreV _ hv)] at hx
    · intro hx
      rwa [hgfixA x hx]
  have hgnotB (x : X) : g x ∉ B := by
    intro hx
    exact Set.disjoint_left.mp havoid ⟨f x, mem_range_self x, (hgf x).symm⟩
      ⟨g x, hx, rfl⟩
  have hgB : collapsesExactly g B := by
    intro x y
    constructor
    · intro hxy
      have he : f x = f y := h.injective (by rw [← hgf x, ← hgf y, hxy])
      rcases (hfAB x y).mp he with he | ⟨hx, hy⟩ | hxyB
      · exact Or.inl he
      · exact Or.inl (by rwa [hgfixA x hx, hgfixA y hy] at hxy)
      · exact Or.inr hxyB
    · rintro (rfl | ⟨hx, hy⟩)
      · rfl
      · have hxy : f x = f y := (hfAB x y).mpr (Or.inr (Or.inr ⟨hx, hy⟩))
        have he : f (g x) = f (g y) := by rw [hgf, hgf, hxy]
        rcases (hfAB (g x) (g y)).mp he with he | ⟨hgx, _⟩ | ⟨hgx, _⟩
        · exact he
        · exact (Set.disjoint_left.mp hAB ((hgA x).mp hgx) hx).elim
        · exact (hgnotB x hgx).elim
  have hgraph : g.graph =
      {p : X × X | f p.2 = h (f p.1)} ∩
        ({p : X × X | f p.1 ∉ V} ∪ {p : X × X | p.2 = p.1}) := by
    ext ⟨x, y⟩
    change g x = y ↔ f y = h (f x) ∧ (f x ∉ V ∨ y = x)
    constructor
    · rintro rfl
      refine ⟨hgf x, ?_⟩
      by_cases hx : f x ∈ V
      · exact Or.inr (hgfix x hx)
      · exact Or.inl hx
    · rintro ⟨hfxy, hxy⟩
      by_cases hx : f x ∈ V
      · exact (hgfix x hx).trans (hxy.resolve_left (not_not.mpr hx)).symm
      · rcases (hfAB (g x) y).mp ((hgf x).trans hfxy.symm) with he | ⟨hgx, _⟩ | ⟨hgx, _⟩
        · exact he
        · exact (hx (hAV ⟨x, (hgA x).mp hgx, rfl⟩)).elim
        · exact (hgnotB x hgx).elim
  have hgcont : Continuous g := by
    apply continuous_of_isClosed_graph
    rw [hgraph]
    exact (isClosed_eq (hf.comp continuous_snd)
      (h.continuous.comp (hf.comp continuous_fst))).inter
        ((hV.preimage (hf.comp continuous_fst)).isClosed_compl.union
          (isClosed_eq continuous_snd continuous_fst))
  refine ⟨g, hgcont, hgB, hgf, hgfix, hgA, hgnotB, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, mem_range_self x, (hgf x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, he⟩
    by_cases hz : z ∈ A
    · exact ⟨z, hgfixA z hz⟩
    · refine ⟨x, ?_⟩
      rcases (hfAB (g x) z).mp ((hgf x).trans he) with he | ⟨_, hzA⟩ | ⟨hgx, _⟩
      · exact he
      · exact (hz hzA).elim
      · exact (hgnotB x hgx).elim

end DifferentialGeometry.Topology
