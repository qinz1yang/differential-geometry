import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# EDP04 kernel: properness of the whole edge restriction and the compact isotopy trace

Frozen blueprint master207B, theorem `thm:fibration-actual-whole-edge-disk-bundle` (EDP04, lines
6949–7038).

* Properness (`isProperMap_restrictPreimage_inter_isClosed`): "For a compact `K ⊂ B₂`, its whole
  inverse image under the GLOBAL continuous `π₂E` is closed in compact `M`; intersecting with the
  globally closed set `V` remains compact and equals the inverse image under this restriction."
  We prove that for any continuous `f` from a compact space to a Hausdorff space, any `B` and any
  closed `V`, the literal restriction `f ⁻¹' B ∩ V → B` is a proper map. This extends X63's
  `isProperMap_restrictPreimage_of_compact` (the case `V = univ`).
* Compact trace (`isCompact_preimage_of_subset_compact_prod`): the time-dependent inverse image of
  the closed target `X_a` under the source family `𝓗 : Y_i × [0,1] → ℝ²` (EI) is closed, and it lies
  in `Q_i × [0,1]` for the compact `Q_i` of EDP03, hence it is compact.

The fibre identification (FC34), the boundary (EV) and the bundle charts are not proved here.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

/-- **EDP04, properness.** The restriction of a continuous map on a compact space to
`f ⁻¹' B ∩ V`, with `V` closed, is a proper map onto its target `B`. -/
theorem isProperMap_restrictPreimage_inter_isClosed {M H : Type*} [TopologicalSpace M]
    [CompactSpace M] [TopologicalSpace H] [T2Space H] {f : M → H} (hf : Continuous f) (B : Set H)
    {V : Set M} (hV : IsClosed V) :
    IsProperMap (fun x : ↥(f ⁻¹' B ∩ V) => (⟨f x, x.2.1⟩ : B)) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨?_, ?_, ?_⟩
  · exact (hf.comp continuous_subtype_val).subtype_mk _
  · intro C hC
    obtain ⟨K, hK, rfl⟩ := isClosed_induced_iff.mp hC
    have himage : (fun x : ↥(f ⁻¹' B ∩ V) => (⟨f x, x.2.1⟩ : B)) '' (Subtype.val ⁻¹' K) =
        Subtype.val ⁻¹' (f '' (K ∩ V)) := by
      ext b
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, ⟨hx, x.2.2⟩, rfl⟩
      · rintro ⟨y, ⟨hyK, hyV⟩, hyb⟩
        refine ⟨⟨y, ?_, hyV⟩, hyK, Subtype.ext hyb⟩
        change f y ∈ B
        rw [hyb]
        exact b.2
    rw [himage]
    exact ((hK.inter hV).isCompact.image hf).isClosed.preimage continuous_subtype_val
  · intro b
    rw [Subtype.isCompact_iff]
    have heq : Subtype.val '' ((fun x : ↥(f ⁻¹' B ∩ V) => (⟨f x, x.2.1⟩ : B)) ⁻¹' {b}) =
        f ⁻¹' {b.1} ∩ V := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨congrArg Subtype.val hz, z.2.2⟩
      · rintro ⟨hx, hxV⟩
        have hxB : f x ∈ B := by
          rw [mem_preimage, mem_singleton_iff] at hx
          rw [hx]
          exact b.2
        exact ⟨⟨x, hxB, hxV⟩, Subtype.ext hx, rfl⟩
    rw [heq]
    exact ((isClosed_singleton.preimage hf).inter hV).isCompact

/-- Compact preimages under the proper edge restriction: for compact `K ⊆ B`, the whole set
`{x ∈ f ⁻¹' B ∩ V | f x ∈ K}` is compact. -/
theorem isCompact_preimage_inter_of_isCompact {M H : Type*} [TopologicalSpace M]
    [CompactSpace M] [TopologicalSpace H] [T2Space H] {f : M → H} (hf : Continuous f)
    {V : Set M} (hV : IsClosed V) {K : Set H} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K ∩ V) :=
  ((hK.isClosed.preimage hf).inter hV).isCompact

/-- **EDP04, compact trace.** For a continuous family `Φ : Y × T → Z` over a compact parameter
space `T` and a closed target `C`, if the whole inverse image lies over a compact `Q ⊆ Y`, it is
compact. -/
theorem isCompact_preimage_of_subset_compact_prod {Y Z T : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace T] [CompactSpace T] {Φ : Y × T → Z}
    (hΦ : Continuous Φ) {C : Set Z} (hC : IsClosed C) {Q : Set Y} (hQ : IsCompact Q)
    (hsub : Φ ⁻¹' C ⊆ Q ×ˢ univ) : IsCompact (Φ ⁻¹' C) :=
  (hQ.prod isCompact_univ).of_isClosed_subset (hC.preimage hΦ) hsub

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
