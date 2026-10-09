import DifferentialGeometry.Topology.Maps.CoincidentGermPairs
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.LocalAtTarget

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry.Topology

/-- On a closed same-value relation, a proper map in the second coordinate
makes the first projection closed. The full product need not be compact. -/
theorem isClosed_fst_image_of_isProperMap
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : IsProperMap g)
    {S : Set (X × Y)} (hS : IsClosed S)
    (hvalue : ∀ p ∈ S, f p.1 = g p.2) :
    IsClosed (Prod.fst '' S) := by
  have hmap : IsClosedMap (Prod.map (id : X → X) g) :=
    (isProperMap_id.prodMap hg).isClosedMap
  have heq : Prod.fst '' S =
      (fun x => (x, f x)) ⁻¹' ((Prod.map (id : X → X) g) '' S) := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      exact ⟨(a, b), hab, Prod.ext rfl (hvalue (a, b) hab).symm⟩
    · rintro ⟨⟨a, b⟩, hab, hp⟩
      exact ⟨(a, b), hab, congrArg Prod.fst hp⟩
  rw [heq]
  exact (hmap S hS).preimage (continuous_id.prodMk hf)

/-- Restricting both domain and codomain over a target subset retains
properness of a continuous map from a compact source. The restricted source
itself is not asserted to be compact. -/
private theorem isProperMap_restrictPreimage_of_compact
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {q : X → Y} (hq : Continuous q) (V : Set Y) :
    IsProperMap (V.restrictPreimage q) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨hq.restrictPreimage, hq.isClosedMap.restrictPreimage V, ?_⟩
  intro y
  apply Subtype.isCompact_iff.mpr
  have heq : ((Subtype.val : (q ⁻¹' V) → X) ''
      ((V.restrictPreimage q) ⁻¹' {y})) = q ⁻¹' {y.val} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val hz
    · intro hx
      have hqx : q x = y.val := hx
      have hxV : x ∈ q ⁻¹' V := by
        change q x ∈ V
        rw [hqx]
        exact y.property
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      exact Subtype.ext hqx
  rw [heq]
  exact (isClosed_singleton.preimage hq).isCompact

/-- The closedness argument used in the compact collision-space supplier
needs only continuity, local injectivity and a Hausdorff target. -/
private theorem isClosed_orderedCollisionPairs_of_local_injectivity
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {q : X → Y} (hq : Continuous q) (hloc : IsLocallyInjective q) :
    IsClosed (orderedCollisionPairs q) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x, y⟩ hxy
  by_cases hqxy : q x = q y
  · have heq : x = y := by
      by_contra hne
      exact hxy ⟨hne, hqxy⟩
    subst y
    obtain ⟨U, hU, hxU, hinj⟩ := hloc x
    apply Filter.mem_of_superset ((hU.prod hU).mem_nhds ⟨hxU, hxU⟩)
    intro z hz hbad
    exact hbad.1 (hinj hz.1 hz.2 hbad.2)
  · apply Filter.mem_of_superset
      ((isClosed_eq (hq.comp continuous_fst)
        (hq.comp continuous_snd)).isOpen_compl.mem_nhds hqxy)
    intro z hz hbad
    exact hz hbad.2

/-- The actual target restriction of a compact-source map has proper
same-value projection. Relative analytic closure and local injectivity suffice
for closedness of the coincident-germ projection on this noncompact source.
Neither properness nor the projected closedness is an input hypothesis. -/
theorem proper_and_isClosed_coincidentGerm_projection_restrictPreimage
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (q : C(X, Y)) (V : Set Y)
    (hloc : IsLocallyInjective (V.restrictPreimage (q : X → Y)))
    (hanalytic : IsClosed
      {p : orderedCollisionPairs (V.restrictPreimage (q : X → Y)) |
        Filter.map (V.restrictPreimage (q : X → Y)) (𝓝 p.1.1) =
          Filter.map (V.restrictPreimage (q : X → Y)) (𝓝 p.1.2)}) :
    IsProperMap (V.restrictPreimage (q : X → Y)) ∧
      IsClosed (Prod.fst '' coincidentGermPairs (V.restrictPreimage (q : X → Y))) := by
  let qr := V.restrictPreimage (q : X → Y)
  have hp : IsProperMap qr := isProperMap_restrictPreimage_of_compact q.continuous V
  have hcollision : IsClosed (orderedCollisionPairs qr) :=
    isClosed_orderedCollisionPairs_of_local_injectivity hp.continuous hloc
  let T := orderedCollisionPairs qr
  let E : Set T := {p | Filter.map qr (𝓝 p.1.1) = Filter.map qr (𝓝 p.1.2)}
  have hE : IsClosed E := hanalytic
  have heq : (Subtype.val : T → (q ⁻¹' V) × (q ⁻¹' V)) '' E =
      coincidentGermPairs qr := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property.1, z.property.2, hz⟩
    · intro hz
      exact ⟨⟨p, hz.1, hz.2.1⟩, hz.2.2, rfl⟩
  have hclosed : IsClosed (coincidentGermPairs qr) := by
    rw [← heq]
    exact hcollision.isClosedEmbedding_subtypeVal.isClosedMap E hE
  exact ⟨hp, isClosed_fst_image_of_isProperMap hp.continuous hp hclosed
    (fun _ h => h.2.1)⟩

end DifferentialGeometry.Topology
