import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedBaseAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSphereFaces

/-!
# FC42 packet T1b: bundle facts of a circle region

Review 40 §3.2 ("紧性与第二可数性"). The fields of `CircleRegion` give
local trivializations `trivialization b : proj⁻¹(neighborhood b) ≃ neighborhood b × S¹` over the
projection, but not the global facts below; they are derived here from the trivializations alone.

* `proj_trivialization_symm`, `proj_preimage_eq_image_trivialization_symm`: the projection read in
  a trivialization;
* `proj_surjective`, `isOpenQuotientMap_proj` (with the tree's `isOpenMap_proj`,
  `Closure/AssemblyCertificateSphereFaces.lean`), `secondCountableTopology_base` (the projection is an
  open surjection from the second-countable domain), `isConnected_proj_fibre` (every fibre is a circle),
  `isConnected_proj_preimage` (preimages of closed connected sets are connected),
  `isCompact_proj_preimage` (preimages of compact sets are compact), `isCompact_rounded` (the rounded
  circle region is compact);

The rim whole-fibre saturation of review 40 §3.2 is NOT re-proved: it is the tree's
`DecompositionCertificate.roundingSupport_handleCorner` (`Closure/AssemblyCertificateSides.lean`),
whose fibre lemma `CircleRegion.isPreconnected_fibre` is the `W`-image form of
`isConnected_proj_fibre` below.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-! ## The projection in a trivialization -/

theorem proj_trivialization_symm (b : R.Base) (y : R.neighborhood b × Circle) :
    R.proj ((R.trivialization b).symm y).val = y.1.val := by
  rw [← R.projection_trivialization b ((R.trivialization b).symm y),
    Diffeomorph.apply_symm_apply]

theorem mem_comap_neighborhood (b : R.Base) {x : R.domain} (hx : R.proj x ∈ R.neighborhood b) :
    x ∈ TopologicalSpace.Opens.comap R.proj (R.neighborhood b) :=
  hx

/-- Over a subset of `neighborhood b`, the preimage of the projection is the trivialization image of
the product with the circle. -/
theorem proj_preimage_eq_image_trivialization_symm (b : R.Base) {A : Set R.Base}
    (hA : A ⊆ R.neighborhood b) :
    R.proj ⁻¹' A = Subtype.val '' ((R.trivialization b).symm ''
      ((Subtype.val ⁻¹' A : Set (R.neighborhood b)) ×ˢ (univ : Set Circle))) := by
  ext x
  constructor
  · intro hx
    have hxb : x ∈ TopologicalSpace.Opens.comap R.proj (R.neighborhood b) := hA hx
    refine ⟨⟨x, hxb⟩, ⟨R.trivialization b ⟨x, hxb⟩, ⟨?_, mem_univ _⟩,
      Diffeomorph.symm_apply_apply _ _⟩, rfl⟩
    change ((R.trivialization b ⟨x, hxb⟩).1 : R.Base) ∈ A
    rw [R.projection_trivialization b ⟨x, hxb⟩]
    exact hx
  · rintro ⟨_, ⟨y, ⟨hy, -⟩, rfl⟩, rfl⟩
    change R.proj ((R.trivialization b).symm y).val ∈ A
    rw [R.proj_trivialization_symm]
    exact hy

/-! ## Global facts -/

theorem proj_surjective : Surjective R.proj := fun b =>
  ⟨((R.trivialization b).symm (⟨b, R.mem_neighborhood b⟩, 1)).val,
    R.proj_trivialization_symm b _⟩

theorem isOpenQuotientMap_proj : _root_.IsOpenQuotientMap R.proj :=
  ⟨R.proj_surjective, R.proj.continuous, R.isOpenMap_proj⟩

/-- The base of a circle region is second countable: the projection is an open surjection from the
second-countable domain. -/
theorem secondCountableTopology_base : SecondCountableTopology R.Base :=
  _root_.Topology.IsOpenQuotientMap.secondCountableTopology R.isOpenQuotientMap_proj

/-- Every fibre of the projection is connected (it is a circle). -/
theorem isConnected_proj_fibre (b : R.Base) : IsConnected (R.proj ⁻¹' {b}) := by
  rw [R.proj_preimage_eq_image_trivialization_symm b
    (singleton_subset_iff.mpr (R.mem_neighborhood b))]
  have hpt : (Subtype.val ⁻¹' {b} : Set (R.neighborhood b)) = {⟨b, R.mem_neighborhood b⟩} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
  rw [hpt]
  exact ((isConnected_singleton.prod isConnected_univ).image _
    (R.trivialization b).symm.continuous.continuousOn).image _ continuous_subtype_val.continuousOn

/-- The preimage of a closed connected subset of the base is connected (the projection is an open
quotient map with connected fibres). -/
theorem isConnected_proj_preimage {K : Set R.Base} (hK : IsClosed K) (hc : IsConnected K) :
    IsConnected (R.proj ⁻¹' K) :=
  R.isOpenQuotientMap_proj.isQuotientMap.isCoinducing.isConnected_preimage_of_isClosed
    R.isConnected_proj_fibre hK hc

/-- Preimages of compact sets under the projection are compact. -/
theorem isCompact_proj_preimage {K : Set R.Base} (hK : IsCompact K) :
    IsCompact (R.proj ⁻¹' K) := by
  have : LocallyCompactSpace R.Base :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) R.Base
  have hloc : ∀ b, ∃ C : Set R.Base, IsCompact C ∧ b ∈ interior C ∧ C ⊆ R.neighborhood b :=
    fun b => exists_compact_subset (R.neighborhood b).isOpen (R.mem_neighborhood b)
  choose C hCc hCb hCsub using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun b => interior (C b)) (fun b => isOpen_interior)
    fun b hb => mem_iUnion.mpr ⟨b, hCb b⟩
  have hcov : R.proj ⁻¹' K = ⋃ b ∈ t, R.proj ⁻¹' (K ∩ C b) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp (ht hx)
      exact ⟨b, hb, hx, interior_subset hxb⟩
    · rintro ⟨b, -, hx, -⟩
      exact hx
  rw [hcov]
  refine t.isCompact_biUnion fun b _ => ?_
  have hsub : K ∩ C b ⊆ R.neighborhood b := inter_subset_right.trans (hCsub b)
  rw [R.proj_preimage_eq_image_trivialization_symm b hsub]
  have hM : IsCompact (Subtype.val ⁻¹' (K ∩ C b) : Set (R.neighborhood b)) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_of_subset (by
      rw [Subtype.range_coe_subtype]
      exact hsub)]
    exact hK.inter_right (hCc b).isClosed
  exact ((hM.prod isCompact_univ).image (R.trivialization b).symm.continuous).image
    continuous_subtype_val

/-- The rounded circle region `R' = proj⁻¹{rounding ≤ 0}` is compact. -/
theorem isCompact_rounded : IsCompact R.rounded :=
  (R.isCompact_proj_preimage R.rounded_compact).image continuous_subtype_val

end CircleRegion

end GC.GraphManifold.Assembly
