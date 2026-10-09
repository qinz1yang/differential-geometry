import DifferentialGeometry.Topology.Ehresmann.FibreProjectionOpenBCF
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Bundles over a loop of the base (lane S-BCF03b; kernels of `circle_base` and of connectedness)

* `preconnectedSpace_of_isOpenMap_fibres_BCF`: a surjective open map with preconnected fibres onto
  a preconnected space has a preconnected total space;
* `exists_circleBase_of_loop_BCF`: over an injective loop `l : S¹ → Bs ⊆ H` (target Hausdorff) the
  union of the whole fibres of a map `f` with local product charts has a continuous OPEN projection
  to `S¹`, `l (p x) = f x` (the field `circle_base` of `EmbeddedFacePartition_BCF`);
* `isPreconnected_preimage_loop_BCF`: that union is preconnected when the fibres are.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology

section Connected

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- **A surjective open map with preconnected fibres onto a preconnected space has a preconnected
total space.** -/
theorem preconnectedSpace_of_isOpenMap_fibres_BCF [PreconnectedSpace β] {g : α → β}
    (hg : IsOpenMap g) (hs : Surjective g) (hfib : ∀ b, IsPreconnected (g ⁻¹' {b})) :
    PreconnectedSpace α := by
  refine ⟨fun u v hu hv huv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩ => ?_⟩
  by_contra hne
  have hdis : ∀ z, z ∈ u → z ∉ v := fun z hzu hzv => hne ⟨z, mem_univ _, hzu, hzv⟩
  have hf : ∀ b, g ⁻¹' {b} ⊆ u ∨ g ⁻¹' {b} ⊆ v := by
    intro b
    by_contra h
    obtain ⟨h1, h2⟩ := not_or.mp h
    obtain ⟨p, hp, hpu⟩ := not_subset.mp h1
    obtain ⟨q, hq, hqv⟩ := not_subset.mp h2
    have hcov : g ⁻¹' {b} ⊆ u ∪ v := fun z _ => huv (mem_univ z)
    have hpv : p ∈ v := (hcov hp).resolve_left hpu
    have hqu : q ∈ u := (hcov hq).resolve_right hqv
    obtain ⟨z, -, hzu, hzv⟩ := hfib b u v hu hv hcov ⟨q, hq, hqu⟩ ⟨p, hp, hpv⟩
    exact hdis z hzu hzv
  have hA : IsOpen (g '' u) := hg u hu
  have hB : IsOpen (g '' v) := hg v hv
  have hcov : (univ : Set β) ⊆ g '' u ∪ g '' v := by
    intro b _
    obtain ⟨z, rfl⟩ := hs b
    rcases huv (mem_univ z) with h | h
    · exact Or.inl ⟨z, h, rfl⟩
    · exact Or.inr ⟨z, h, rfl⟩
  have hAne : (univ ∩ g '' u).Nonempty := ⟨g x, mem_univ _, x, hxu, rfl⟩
  have hBne : (univ ∩ g '' v).Nonempty := ⟨g y, mem_univ _, y, hyv, rfl⟩
  obtain ⟨b, -, ⟨z, hzu, hzb⟩, ⟨z', hz'v, hz'b⟩⟩ :=
    (isPreconnected_univ (α := β)) _ _ hA hB hcov hAne hBne
  have hzF : z ∈ g ⁻¹' {b} := hzb
  have hz'F : z' ∈ g ⁻¹' {b} := hz'b
  rcases hf b with h | h
  · exact hdis z' (h hz'F) hz'v
  · exact hdis z hzu (h hzF)

end Connected

section Loop

variable {E Q Wt H : Type*} [TopologicalSpace E] [TopologicalSpace Q] [TopologicalSpace Wt]
  [TopologicalSpace H] [T2Space H] {X : Set Wt} {f : Wt → H} {Bs : Set H} {l : Circle → H}

/-- **The projection of the bundle over a loop of the base to the circle** (`circle_base`): a
continuous open map `p` with `l (p x) = f x`. -/
theorem exists_circleBase_of_loop_BCF (hlc : Continuous l) (hli : Injective l)
    (hlB : range l ⊆ Bs) (hfc : ContinuousOn f X)
    (hchart : ∀ y ∈ range l, ∃ (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E), σ x₀ = y ∧
      IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs ∩ O ∧ Continuous φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x) :
    ∃ p : (X ∩ f ⁻¹' range l : Set Wt) → Circle, Continuous p ∧ IsOpenMap p ∧
      ∀ x, l (p x) = f x := by
  have hemb : IsEmbedding l := (hlc.isClosedEmbedding hli).isEmbedding
  let g : Circle ≃ₜ range l := hemb.toHomeomorph
  let π : (X ∩ f ⁻¹' range l : Set Wt) → range l := fun q => ⟨f q, q.2.2⟩
  have hπo : IsOpenMap π := isOpenMap_restrict_fibreProj_BCF hlB hchart
  have hπc : Continuous π :=
    (hfc.comp_continuous continuous_subtype_val fun q => q.2.1).subtype_mk _
  refine ⟨fun q => g.symm (π q), g.symm.continuous.comp hπc, g.symm.isOpenMap.comp hπo, ?_⟩
  intro q
  have h := congrArg Subtype.val (g.apply_symm_apply (π q))
  exact h

omit [T2Space H] in
/-- **The bundle over a loop of the base is preconnected** when its fibres are. -/
theorem isPreconnected_preimage_loop_BCF (hlc : Continuous l) (hlB : range l ⊆ Bs)
    (hchart : ∀ y ∈ range l, ∃ (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E), σ x₀ = y ∧
      IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs ∩ O ∧ Continuous φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x)
    (hne : ∀ y ∈ range l, (X ∩ f ⁻¹' {y}).Nonempty)
    (hfib : ∀ y ∈ range l, IsPreconnected (X ∩ f ⁻¹' {y})) :
    IsPreconnected (X ∩ f ⁻¹' range l) := by
  let π : (X ∩ f ⁻¹' range l : Set Wt) → range l := fun q => ⟨f q, q.2.2⟩
  have hπo : IsOpenMap π := isOpenMap_restrict_fibreProj_BCF hlB hchart
  have : PreconnectedSpace (range l) := Subtype.preconnectedSpace (isPreconnected_range hlc)
  have hπs : Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨q, hqX, hqy⟩ := hne y hy
    have hqy' : f q = y := hqy
    exact ⟨⟨q, hqX, by rw [mem_preimage, hqy']; exact hy⟩, Subtype.ext hqy'⟩
  have hfib' : ∀ b, IsPreconnected (π ⁻¹' {b}) := by
    rintro ⟨y, hy⟩
    have himg : Subtype.val '' (π ⁻¹' {⟨y, hy⟩}) = X ∩ f ⁻¹' {y} := by
      ext q
      constructor
      · rintro ⟨q', hq', rfl⟩
        have : f q' = y := congrArg Subtype.val hq'
        exact ⟨q'.2.1, this⟩
      · rintro ⟨hqX, hqy⟩
        have hqy' : f q = y := hqy
        exact ⟨⟨q, hqX, by rw [mem_preimage, hqy']; exact hy⟩, Subtype.ext hqy', rfl⟩
    exact (Topology.IsInducing.subtypeVal.isPreconnected_image).mp (himg ▸ hfib y hy)
  have hP : PreconnectedSpace (X ∩ f ⁻¹' range l : Set Wt) :=
    preconnectedSpace_of_isOpenMap_fibres_BCF hπo hπs hfib'
  have := (isPreconnected_univ (α := (X ∩ f ⁻¹' range l : Set Wt))).image Subtype.val
    continuous_subtype_val.continuousOn
  rwa [image_univ, Subtype.range_coe] at this

end Loop

end DifferentialGeometry.Topology
