import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-!
# O-WF G1c: two topological kernels of the local one-sheet route

* `eqOn_of_isPreconnected_of_locInjOn_OWF` (local constancy): a map `h` continuous on a
  preconnected set `L`, with values in a set `Z` on which a coordinate `κ` is LOCALLY injective
  around every `h x` (`InjOn κ (Z ∩ V)`, `V` open), and `κ ∘ h` constant on `L`, is constant on
  `L`. (Used with `h = f_st⁰`, `L` the whole adjusted level, `Z` the native zero set: the native
  map is constant on each adjusted level, so the final map is too.)
* `isEmbedding_of_proper_factor_OWF` (no merging as an embedding): if `f = Θ ∘ f₀` on `X`, `f₀`
  continuous on `X`, `Θ` continuous on `f₀(X)`, `f|X` proper over the compact subsets of
  `B = Θ(f₀(X))` (metric target) and `f₀` is constant on the fibres of `f|X`, then `Θ` restricted
  to `f₀(X)` is a topological embedding. Route: `f|X : X → B` is proper (Hausdorff, sequential
  target), hence closed, hence a quotient map; the inverse `B → f₀(X)` is continuous because its
  composite with `f|X` is `f₀|X`; a continuous left inverse makes `Θ|` an embedding.
-/

set_option autoImplicit false

open Set Function Filter Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- **Local constancy on a preconnected set** (see the module docstring). -/
theorem eqOn_of_isPreconnected_of_locInjOn_OWF {α Y Z : Type*} [TopologicalSpace α]
    [TopologicalSpace Y] {L : Set α} (hL : IsPreconnected L) {h : α → Y} (hh : ContinuousOn h L)
    {Zs : Set Y} (hZ : ∀ x ∈ L, h x ∈ Zs) (κ : Y → Z) {c : Z} (hκ : ∀ x ∈ L, κ (h x) = c)
    (hloc : ∀ x ∈ L, ∃ V : Set Y, IsOpen V ∧ h x ∈ V ∧ InjOn κ (Zs ∩ V)) :
    ∀ x ∈ L, ∀ x' ∈ L, h x = h x' := by
  have : PreconnectedSpace L := Subtype.preconnectedSpace hL
  let f : L → Y := fun x => h x
  have hf : Continuous f := hh.domRestrict
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨V, hV, hxV, hinj⟩ := hloc x x.2
    have hpre : f ⁻¹' V ∈ 𝓝 x := hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV)
    filter_upwards [hpre] with x' hx'
    exact hinj ⟨hZ x' x'.2, hx'⟩ ⟨hZ x x.2, hxV⟩ ((hκ x' x'.2).trans (hκ x x.2).symm)
  intro x hx x' hx'
  exact hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨x', hx'⟩

/-- **No merging as a topological embedding** (see the module docstring). -/
theorem isEmbedding_of_proper_factor_OWF {M Y' Y : Type*} [TopologicalSpace M]
    [TopologicalSpace Y'] [MetricSpace Y] {X : Set M} {f₀ : M → Y'} {Θ : Y' → Y}
    (hf₀ : ContinuousOn f₀ X) (hΘ : ContinuousOn Θ (f₀ '' X))
    (hprop : ∀ K ⊆ Θ '' (f₀ '' X), IsCompact K →
      IsCompact (X ∩ (fun p => Θ (f₀ p)) ⁻¹' K))
    (hinj : ∀ p ∈ X, ∀ p' ∈ X, Θ (f₀ p) = Θ (f₀ p') → f₀ p = f₀ p') :
    Topology.IsEmbedding (fun x : f₀ '' X => Θ x) := by
  set D := f₀ '' X with hD
  set B := Θ '' D with hB
  let f₀X : X → D := fun p => ⟨f₀ p, mem_image_of_mem f₀ p.2⟩
  let g' : D → B := fun x => ⟨Θ x, mem_image_of_mem Θ x.2⟩
  let fX : X → B := fun p => g' (f₀X p)
  have hf₀X : Continuous f₀X := hf₀.domRestrict.subtype_mk _
  have hg' : Continuous g' := hΘ.domRestrict.subtype_mk _
  have hfX : Continuous fX := hg'.comp hf₀X
  have hsurj : Surjective fX := by
    rintro ⟨b, x, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩
  have : CompactlyCoherentSpace B := inferInstance
  have hproper : IsProperMap fX := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hfX, fun K hK => ?_⟩
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have himg : Subtype.val '' (fX ⁻¹' K) = X ∩ (fun p => Θ (f₀ p)) ⁻¹' (Subtype.val '' K) := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.2, fX q, hq, rfl⟩
      · rintro ⟨hpX, b, hbK, hb⟩
        refine ⟨⟨p, hpX⟩, ?_, rfl⟩
        have : fX ⟨p, hpX⟩ = b := Subtype.ext hb.symm
        change fX ⟨p, hpX⟩ ∈ K
        rw [this]
        exact hbK
    rw [himg]
    refine hprop _ ?_ (hK.image continuous_subtype_val)
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hq : Topology.IsQuotientMap fX := hproper.isClosedMap.isQuotientMap hfX hsurj
  let φ : B → D := fun b => f₀X (surjInv hsurj b)
  have hφfX : φ ∘ fX = f₀X := by
    funext p
    set p'' : X := surjInv hsurj (fX p) with hp''
    have h1 : fX p'' = fX p := surjInv_eq hsurj (fX p)
    have h2 : Θ (f₀ (p'' : M)) = Θ (f₀ (p : M)) := congrArg Subtype.val h1
    exact Subtype.ext (hinj _ p''.2 _ p.2 h2)
  have hφ : Continuous φ := hq.continuous_iff.mpr (by rw [hφfX]; exact hf₀X)
  have hleft : LeftInverse φ g' := by
    rintro ⟨x, p, hp, rfl⟩
    exact congrFun hφfX ⟨p, hp⟩
  exact Topology.IsEmbedding.subtypeVal.comp (hleft.isEmbedding hφ hg')

end DifferentialGeometry.Geometry.Collapse
